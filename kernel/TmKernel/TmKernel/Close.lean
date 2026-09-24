import TmKernel.Cmd
/-!
# `close`: §6.3's lifecycle, one fold at three grains

§6.3 writes three rows — `close day`, `close week`, `close month` — and
`horizon.rs` implements them as three functions with three targets and a
sixteen-period catch-up loop.  Here they are **one fold** over the ids whose
live line sits in a closed region of grain `g`, filing each into
`closeTo g now` (Grain.lean) — the block of the next coarser grain that
contains *now*, which `closeTo_target_is_open` says is never itself closed.
That is the owner's decision D1 (2026-09-12): `closeTo`, never
`targetContaining`, at every grain, the day row included.

What the three rows do **not** share is tabulated, not derived (AGENTS §5.5):
humans wrote §6.3, so which boxes count as unfinished, whether the line is moved
or copied, which section it lands in, which stamp it gains, and what is exempt
are data.  That data is `ClosePolicy`, one row per `Grain`, and every row is
pinned by a bridge theorem that ties it to something the row does not itself
say — the stamp to `Field.Stamp`'s grain, the `# Demoted` landing to the month
file `closeTo` reaches, the copy to the grains below month — so corrupting a row
is a build failure, not a silent behaviour change.

What is derived: the target region (`closeTo`), the file kind of a grain
(`kindOfGrain`), and the stamp's *number* (the civil day of month, the ISO week)
from the closed region's index.

**The shape of the proof.**  Every step of the fold either leaves the plan
alone or relocates one id through `WfPlan.mapAt` — after, for a line that lands
inside a section, a rank shift of the destination file that makes room — and
both re-run the whole of `planWf` by computation.  The theorems are stated over
a rank-free skeleton of each entity (`Skel`: its file, its tombstone's file and
bytes, its box, its bytes), because a shift moves ranks and nothing else, and
over the files' kinds and regions (`Frame`), which no step changes.
`close_spec` is the denotation: after a successful close, every id's skeleton is
`stepSkel` of its skeleton before (`close_skel`, per id), and no line is one the
same close would take again.  Everything else is read off it.

**Scoped out of this module, by name** (README stage-4 step-2 block, with gaps
53–57 for what the fold does refuse or does not write): the day file's review
section (F3, stage 6), and `est:` = remaining beyond the line's own reading (the
log's minutes and the rollup).  The estimates a close does write are L15's floor
from a standing record it merges into (README gap 53,
`close_week_merges_a_standing_record_it_does_not_drop`) and the child fold's.

**Unfinished children are dropped, their remaining folded by §6.4's `max` (goal B3's
repair, stage 4 final step 4).**  §6.3's week row: "Unfinished children are dropped
from the week file (their remaining is folded into the parent's `est:`)".  A line the
week close files whose `@parent` is another line it files from the same file is
dropped — `[~]` in place; the kernel removes no line, where fork-point `close_week`
deleted it — and its own remaining goes to the nearest such ancestor that is not
itself dropped (`dropsInto`), whose record carries `max(what it carried, Σ own
remaining of the children dropped with it)` (`close_week_folds_dropped_children_by_max`,
fork-point `horizon::demote_est`'s `folded`).  The fold needs the block length, so
`close` takes it: `close g now bm`.  Goal B3's additive statement double-counted and is
refuted (`close_week_does_not_add_a_dropped_child_to_its_parent`, Boundary.lean).

**Dated work routes itself (the owner's D7 and D8, 2026-09-13; README gap 55).**
The week row's "dated items past due with `persist` → moved to
`backlog.md#Overdue` instead" is performed: a line whose `due:` day (or an
interval's end day) is before `now`'s, with §5.3's `on_miss` resolving to
`persist`, is a fourth action, `CloseAct.overdue` — moved to the end of the backlog's
`# Overdue` with its box, its bytes and its tombstone as they were, no stamp and
no tombstone left (`close_moves_a_past_due_persist_line_to_the_backlog`).  Day
resolution, as the wall carry's (README gap 57).  A backlog has no region, so no
close ever takes a line from it again (`stepSkel_lands_outside_every_closed_region`,
L16).  A not-yet-due dated line is filed like any other and keeps its `due:` in
its `# Demoted` record, which `shapesWf` admits since D8
(`close_week_demotes_a_not_yet_due_line_it_does_not_drop_keeping_its_date`).
-/
namespace Tm

open Field (Stamp Recur Shape DT)

/-! ## `ClosePolicy` — §6.3's residue, one row per grain -/

/-- What a close does with a line it takes. -/
inductive Disposition
  /-- the line leaves its file and nothing stays behind (§6.3's month row) -/
  | move
  /-- the line leaves and its box reopens: `[>]` → `[ ]` (§6.3's day row) -/
  | moveReopening
  /-- `[-]` stays behind as the tombstone and the stamped record is filed
      forward (§6.3's week row — `refile`: `demote`, or a merge into the item's
      standing `# Demoted` record, README gap 53) -/
  | copy
deriving DecidableEq, Repr

/-- Where in the destination file the line lands. -/
inductive Landing
  /-- after every line the file has (§6.3's day row: "moved to `week/<current>`") -/
  | fileEnd
  /-- at the end of the `# Demoted` section (§6.3's week row, §4.2) -/
  | demotedSection
  /-- at the end of the section with the heading it stood under (§6.3's month
      row: "each into the section it came from" is `horizon.rs`'s reading) -/
  | sameSection
  /-- at the end of `backlog.md`'s `# Overdue` section (§6.3's week row, fork-point
      `OVERDUE_SECTION`; the owner's D7) -/
  | overdueSection
deriving DecidableEq, Repr

/-- Which stamp a taken line gains.  The *number* is derived from the closed
region; the table only picks the rule. -/
inductive StampRule
  | none
  /-- `demoted:D07` — the civil day of month of the closed day -/
  | dayOfMonth
  /-- `demoted:W37` — the ISO week number of the closed week -/
  | isoWeek
deriving DecidableEq, Repr

/-- What happens to a line §6.3's last paragraph exempts. -/
inductive Exemption
  /-- left exactly where it is -/
  | stays
  /-- moved, undemoted, into the live week — so the planner still sees it
      (fork-point `close_week`'s wall carry, F4) — when it is still ahead -/
  | carried
deriving DecidableEq, Repr

/-- What a row does with an unfinished child of a line it files from the same file.
(This column was `Owed`, the table's last scope-out — `nothing | childFoldB3`, and
before that gap22Parent and stage5OnMiss — until goal B3's repair made the fold
real, stage 4 final step 4; the table owes nothing now.) -/
inductive ChildRule
  /-- nothing of its own: the child is taken, or not, like any other line -/
  | asAnyLine
  /-- §6.3's week row: "Unfinished children are dropped from the week file (their
      remaining is folded into the parent's `est:`)" — `[~]` in place, and its own
      remaining folded into the nearest ancestor the close files from that file, by
      §6.4's `max` (`foldEst`, fork-point `demote_est`'s `folded`) -/
  | dropIntoParent
deriving DecidableEq, Repr

/-- What a row does with a dated line that is past due with `on_miss = persist`
(§5.3: the default of a point and an interval; `on-miss:` overrides it). -/
inductive OverdueRule
  /-- nothing of its own: the line is taken, or not, like any other line -/
  | asAnyLine
  /-- moved to the end of `backlog.md`'s `# Overdue`, box, bytes and tombstone
      kept (§6.3's week row, "moved to `backlog.md#Overdue` instead"; the owner's
      D7, pulled forward from stage 5) -/
  | toBacklogOverdue
deriving DecidableEq, Repr

/-- **§6.3's residue.**  Everything the three close rows do not share. -/
structure ClosePolicy where
  /-- which boxes count as "unfinished" -/
  takes       : Status → Bool
  disposition : Disposition
  landing     : Landing
  stamp       : StampRule
  /-- recurring items: "never demoted — their instances expire or persist" -/
  recurring   : Exemption
  /-- walls — dated intervals: §6.3's "calendar intervals are never demoted" -/
  walls       : Exemption
  /-- the week row's "dated items past due with `persist` → `backlog.md#Overdue`" -/
  overdue     : OverdueRule
  /-- the week row's "unfinished children are dropped … folded into the parent's `est:`" -/
  children    : ChildRule

/-- §6.3's day and week rows: "`[ ]`/`[>]`". -/
def Status.isOpenBox : Status → Bool
  | .live .free => true
  | .live .self => true
  | _           => false

/-- §6.3's month row: "unfinished outcomes and everything in `# Demoted`" —
every box that is not settled, the `[-]` record included. -/
def Status.isUnsettled : Status → Bool
  | .settled _ => false
  | _          => true

/-- **The table.** -/
def closePolicy : Grain → ClosePolicy
  | ⟨0, _⟩ => { takes := Status.isOpenBox, disposition := .moveReopening,
                landing := .fileEnd, stamp := .dayOfMonth,
                recurring := .stays, walls := .carried,
                overdue := .asAnyLine, children := .asAnyLine }
  | ⟨1, _⟩ => { takes := Status.isOpenBox, disposition := .copy,
                landing := .demotedSection, stamp := .isoWeek,
                recurring := .stays, walls := .carried,
                overdue := .toBacklogOverdue, children := .dropIntoParent }
  | _      => { takes := Status.isUnsettled, disposition := .move,
                landing := .sameSection, stamp := .none,
                recurring := .stays, walls := .carried,
                overdue := .asAnyLine, children := .asAnyLine }

/-- The file kind a grain names — §2's layout, derived: a grain's blocks are
the `day/`, `week/` and `month/` files.  (`calendar/` files share week regions
and are generated; no close takes a line from one.) -/
def kindOfGrain : Grain → DocKind
  | ⟨0, _⟩ => .day
  | ⟨1, _⟩ => .week
  | _      => .month

/-- The stamp a rule names for a closed region's index.  Derived arithmetic:
a day region's index is the day, and a week region's is the ISO week ordinal
whose Monday is `7 * ix` (the kernel's day 0 is a Monday). -/
def stampRuleOf : StampRule → Nat → Option Stamp
  | .none,       _  => none
  | .dayOfMonth, ix => some (.day (Cal.ofDay ix).day)
  | .isoWeek,    ix => some (.week (Cal.isoOf (7 * ix)).week)

/-- The stamp closing grain `g`'s region `ix` appends. -/
def closeStamp (g : Grain) (ix : Nat) : Option Stamp := stampRuleOf (closePolicy g).stamp ix

/-- The grain a stamp names — `Field.Stamp` has no month constructor, which is
why a month close cannot stamp. -/
def Field.Stamp.grain : Stamp → Grain
  | .day _  => Tm.day
  | .week _ => Tm.week

/-! ### The bridges: a corrupted row is a build failure -/

/-- **Stamp accrual.**  A close stamps the grain it closed and no other — so
the month review's "≥ 2 stamps" cut list cannot count a day stamp as a week
stamp, and a month close cannot invent a stamp at all. -/
theorem closeStamp_names_the_closed_grain (g : Grain) (ix : Nat) (s : Stamp)
    (h : closeStamp g ix = some s) : s.grain = g := by
  match g with
  | ⟨0, _⟩ => simp only [closeStamp, closePolicy, stampRuleOf, Option.some.injEq] at h; subst h; rfl
  | ⟨1, _⟩ => simp only [closeStamp, closePolicy, stampRuleOf, Option.some.injEq] at h; subst h; rfl
  | ⟨2, _⟩ => simp [closeStamp, closePolicy, stampRuleOf] at h

/-- A month close carries stamps and adds none (§6.3: "demoted items keep
stamps"). -/
theorem closeStamp_month (ix : Nat) : closeStamp month ix = none := rfl

/-- **"For each unfinished item."**  No row takes a settled line. -/
theorem close_never_takes_a_settled_line (g : Grain) (o : Outcome) :
    (closePolicy g).takes (.settled o) = false := by
  match g with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

/-- The month row takes the `[-]` records of `# Demoted` (§6.3: "everything in
`# Demoted`"); the rows below it do not re-take one. -/
theorem closePolicy_takes_the_demoted_record_only_at_month (g : Grain) :
    (closePolicy g).takes .demoted = decide (g = month) := by
  match g with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

/-- **The `# Demoted` landing is a month-file section** (§4.2, and
`headingsWf`): the only row that files into it is one whose `closeTo` reaches a
month file. -/
theorem closePolicy_demoted_landing_is_in_a_month_file :
    ∀ g : Grain, (closePolicy g).landing = .demotedSection → kindOfGrain (coarsen g) = .month := by
  decide

/-- **Only a grain below month leaves a tombstone.**  §6.3's month row *moves*
the record; the week row over an item that already has one merges into it
(`refile`, README gap 53), and a `[-]` record filed again is `KErr.alreadyDemoted`. -/
theorem closePolicy_copies_only_below_month :
    ∀ g : Grain, (closePolicy g).disposition = .copy → g ≠ month := by
  decide

/-- A copy writes a `demoted:` stamp, so a copying row must name one — the
`none` branch of `fileE` below is unreachable from the table. -/
theorem closePolicy_copy_stamps :
    ∀ g : Grain, (closePolicy g).disposition = .copy → (closePolicy g).stamp ≠ .none := by
  decide

/-- A plain move writes no stamp (it is `moveTo`), so a moving row must not
name one. -/
theorem closePolicy_move_is_unstamped :
    ∀ g : Grain, (closePolicy g).disposition = .move → (closePolicy g).stamp = .none := by
  decide

/-- **§6.3's last paragraph, at every grain.**  Recurring items stay; walls are
carried, never demoted. -/
theorem closePolicy_exemptions :
    ∀ g : Grain, (closePolicy g).recurring = .stays ∧ (closePolicy g).walls = .carried := by
  decide

/-- **The child fold's column, bridged** (restates `closePolicy_owes_only_the_child_fold`,
whose `Owed` column is gone: the fold it owed is performed).  Only §6.3's week row
drops a child into its parent — the day row moves pinned leftovers one by one, and
the month row carries records and outcomes, each on its own. -/
theorem closePolicy_drops_children_only_at_week :
    ∀ g : Grain, (closePolicy g).children = .dropIntoParent ↔ g = week := by
  decide

/-- **The fold lands in a record.**  A row that drops children copies the line it
files, so the children's minutes have a `# Demoted` record to be floored into
(`refiledLineX`); a moving row would have nowhere to write them. -/
theorem closePolicy_drops_children_only_at_a_copying_row :
    ∀ g : Grain, (closePolicy g).children = .dropIntoParent → (closePolicy g).disposition = .copy := by
  decide

/-- **D7's column, bridged.**  Only §6.3's week row routes a past-due `persist`
line to the backlog — the day row's pinned leftovers go to the week of now, and
the month row carries its records forward, dated or not (README "Stage 4 final",
D8's cost (ii)). -/
theorem closePolicy_routes_overdue_only_at_week :
    ∀ g : Grain, (closePolicy g).overdue = .toBacklogOverdue ↔ g = week := by
  decide

/-! ## The skeleton an entity keeps through a close

A close relocates lines, and a line landing inside a section shifts the ranks
below it.  Neither a relocation nor a shift touches what any §6.3 statement is
about, so the statements are made over what is left when ranks are forgotten. -/

/-- An entity without its ranks: which file its record is in, which file its
tombstone is in and what the tombstone says, its box, and its bytes. -/
structure Skel where
  doc      : DocIx
  archDoc  : Option DocIx
  archLine : Option RawItem
  status   : Status
  line     : RawItem
deriving DecidableEq, Repr

def Core.skel (c : Core) : Skel :=
  ⟨c.live.doc, c.archive.map (fun t => t.site.doc), c.archive.map Tomb.line, c.status, c.line⟩

/-- §3.1's `stamps`, off a skeleton — `Core.stamps` of any core with these bytes. -/
def Skel.stamps (s : Skel) : List Stamp := (Field.viewDemoted s.line).getD []

theorem Core.skel_stamps (c : Core) : c.skel.stamps = c.stamps := rfl

/-- Recurring, read off the bytes (`Core.recur`). -/
def Skel.recurring (s : Skel) : Bool := decide (Field.viewRecur s.line ≠ Recur.none)

/-- A wall — a dated interval, read off the bytes (`Core.shape`) — and whether
it is still ahead of `now`.  Day resolution (README gap 10): a wall ending on
`now`'s day counts as ahead, so a close never strands one that may not be over. -/
def Skel.wallAhead (now : Day) (s : Skel) : Option Bool :=
  match Field.viewShape s.line with
  | .interval _ b => some (decide (now ≤ b.day))
  | _             => none

/-- §5.3's `on_miss`, read off the bytes: the `on-miss:` token if the line carries
one, else the shape's default (`effectiveOnMiss` of any core with these bytes). -/
def Skel.onMiss (s : Skel) : Field.OnMiss :=
  (Field.viewOnMiss s.line).getD (defaultOnMiss (Field.viewShape s.line))

theorem Core.skel_onMiss (c : Core) : c.skel.onMiss = effectiveOnMiss c := rfl

/-- The day a dated line falls due, read off the bytes: a point's `due:` day, an
interval's end day.  `none` for every other shape — a window is a chance that
passes, never overdue (fork-point `overdue_at`'s `_ => false`). -/
def Skel.dueDay (s : Skel) : Option Nat :=
  match Field.viewShape s.line with
  | .point m      => some m.day
  | .interval _ b => some b.day
  | _             => none

/-- **Past due at `now`, with `persist`** — fork-point `horizon::overdue_at` (a
point: `due.end_of_day() < now`; an interval: `end < now`; only when `on_miss` is
`persist`), at **day resolution**: the due day is strictly before `now`'s day.
The kernel's `now` is a `Day` (README gap 57, the wall carry's rule), so a line
due at 08:00 on the day a close runs at 09:00 is not yet past due here and is
demoted with its date instead (README "Stage 4 final", step 2's recorded
difference).  A bare date and a date-time on one day agree with the Rust, which
reads a bare date as 23:59. -/
def Skel.overdue (now : Day) (s : Skel) : Bool :=
  match s.dueDay with
  | some d => decide (d < now) && decide (s.onMiss = .persist)
  | none   => false

/-- A wall still ahead is not past due: the two rules read one end day. -/
theorem Skel.overdue_of_wallAhead {now : Day} {s : Skel} (h : s.wallAhead now = some true) :
    s.overdue now = false := by
  unfold Skel.wallAhead at h
  unfold Skel.overdue Skel.dueDay
  cases hv : Field.viewShape s.line with
  | interval a b =>
    rw [hv] at h
    simp only [Option.some.injEq, decide_eq_true_eq] at h
    simp [Nat.not_lt.2 h]
  | none => simp [hv] at h
  | point m => simp [hv] at h
  | window r d => simp [hv] at h

/-- The files' kinds and regions, which no step of a close changes. -/
def Frame (p q : PlanCore) : Prop :=
  q.docs.length = p.docs.length ∧ (∀ k, docKindAt q k = docKindAt p k) ∧
    (∀ k, docRegion q k = docRegion p k)

theorem Frame.refl (p : PlanCore) : Frame p p := ⟨rfl, fun _ => rfl, fun _ => rfl⟩

theorem Frame.trans {p q r : PlanCore} (h1 : Frame p q) (h2 : Frame q r) : Frame p r :=
  ⟨h2.1.trans h1.1, fun k => (h2.2.1 k).trans (h1.2.1 k), fun k => (h2.2.2 k).trans (h1.2.2 k)⟩

/-! ## Which lines a close takes, and what it does with each -/

/-- The closed region of grain `g` document `k` is, if it is one: a file of the
grain's own kind whose region has that grain and is `Closed` at `now`. -/
def closedRegionOf (g : Grain) (now : Day) (p : PlanCore) (k : DocIx) : Option Region :=
  match docRegion p k with
  | none   => none
  | some r => if docKindAt p k = kindOfGrain g ∧ r.grain = g ∧ Closed r now then some r else none

/-- What one close step does to one line. -/
inductive CloseAct
  | stay
  | carry
  /-- filed forward, out of the closed region `r` -/
  | file (r : Region)
  /-- past due with `persist`: moved, undemoted, to `backlog.md # Overdue` (D7) -/
  | overdue
deriving DecidableEq, Repr

def exemptAct : Exemption → Bool → CloseAct
  | .stays,   _     => .stay
  | .carried, true  => .carry
  | .carried, false => .stay

/-- **The candidate set and the action, as one function of the plan's files
and the line's skeleton.**  A line not in a closed region of grain `g` stays; so
does one whose box the row does not take.  A recurring line gets its exemption; a
line past due with `persist`, at a row that routes it, goes to the backlog's
`# Overdue` (D7 — before the wall test, as fork-point `close_week` classifies
`overdue` before `carried_walls`, so a wall that is over with `persist` is overdue
and one with `on-miss:expire`/`next` stays); a wall gets its exemption; everything
else is filed. -/
def closeAct (g : Grain) (now : Day) (p : PlanCore) (s : Skel) : CloseAct :=
  match closedRegionOf g now p s.doc with
  | none   => .stay
  | some r =>
    if (closePolicy g).takes s.status = false then .stay
    else if s.recurring then exemptAct (closePolicy g).recurring true
    else if (closePolicy g).overdue = .toBacklogOverdue ∧ s.overdue now = true then .overdue
    else match s.wallAhead now with
      | some ahead => exemptAct (closePolicy g).walls ahead
      | none       => .file r

/-- The first document of a kind whose region is `r`.  The kernel cannot create
a file — it has regions and no path grammar (README gap 10) — so a target the
host did not hand over is a refusal, `noTarget`, and never a guess. -/
def findDocIx (p : PlanCore) (kind : DocKind) (r : Region) : Option DocIx :=
  (List.range p.docs.length).find? (fun k => decide (docKindAt p k = kind ∧ docRegion p k = some r))

/-- **D1's target.**  The file of the next coarser grain containing `now`. -/
def closeTarget (g : Grain) (now : Day) (p : PlanCore) : Option DocIx :=
  findDocIx p (kindOfGrain (coarsen g)) (closeTo g now)

/-- Where a carried wall goes: the week containing `now` — the one week file
the planner still reads (§6.2). -/
def carryTarget (now : Day) (p : PlanCore) : Option DocIx :=
  findDocIx p .week (regionOf week now)

/-- **Where a past-due `persist` line goes (D7)**: the backlog — the document of
kind `backlog` with no region, "the **absence** of a bound" (`Doc.region`).  The
kernel cannot create it (README gap 56), so a request without one refuses
`noTarget`; and a backlog declared with a region is not one (`pathsDistinct`
allows one `backlog.md`, and the host declares none). -/
def overdueTarget (p : PlanCore) : Option DocIx :=
  (List.range p.docs.length).find? (fun k => decide (docKindAt p k = .backlog ∧ docRegion p k = none))

/-- §6.3's day row: `[>]` → `[ ]`. -/
def reopen : Status → Status
  | .live .self => .live .free
  | s           => s

/-- The bytes with a stamp appended, if the row names one. -/
def stampedLine (os : Option Stamp) (s : Skel) : RawItem :=
  match os with
  | none    => s.line
  | some st => Field.setDemoted (s.stamps ++ [st]) s.line

/-- The skeleton filing a line out of region `r` into document `k` leaves — with the
week row's child fold `x` applied to a copied record's estimate. -/
def skelAfter (g : Grain) (r : Region) (k : DocIx) (x : FoldFx) (s : Skel) : Skel :=
  match (closePolicy g).disposition with
  | .move          => { s with doc := k }
  | .moveReopening => { s with doc := k, status := reopen s.status,
                               line := stampedLine (closeStamp g r.ix) s }
  | .copy          =>
    match closeStamp g r.ix with
    | some st => ⟨k, some s.doc, some s.line, .demoted, refiledLineX x st s.archLine s.line⟩
    | none    => s

/-- **The denotation of one step, on a skeleton**, given what the week row's child
fold asks of the line (`x`, `foldFxOf`).  A line filed as a child dropped with its
parent keeps its file, its tombstone and its bytes and becomes `[~]`.  The branches
with no target are the ones in which `close` refuses; they return the skeleton
unchanged, which no theorem below reads. -/
def stepSkel (g : Grain) (now : Day) (p : PlanCore) (x : FoldFx) (s : Skel) : Skel :=
  match closeAct g now p s with
  | .stay   => s
  | .carry  =>
    match carryTarget now p with
    | some k => { s with doc := k }
    | none   => s
  | .file r =>
    if x.isDrop then { s with status := .settled .dropped }
    else match closeTarget g now p with
    | some k => skelAfter g r k x s
    | none   => s
  | .overdue =>
    match overdueTarget p with
    | some k => { s with doc := k }
    | none   => s

/-! ## Landing: the rank a line takes, and the shift that makes room

A plan's ranks come from line numbers, so a section that is not the last one
has no free rank at its end.  Landing inside it shifts every rank of the
destination file at or after the next heading up by one, and the line takes the
freed rank — which is at the end of the section and before that heading.  The
shift re-runs `planWf` by computation like every other post-state. -/

def shiftRank (n0 r : Nat) : Nat := if n0 ≤ r then r + 1 else r

def Site.shiftIn (k n0 : Nat) (s : Site) : Site :=
  if s.doc = k then ⟨s.doc, shiftRank n0 s.rank⟩ else s

theorem Site.shiftIn_doc (k n0 : Nat) (s : Site) : (s.shiftIn k n0).doc = s.doc := by
  unfold Site.shiftIn; split <;> rfl

def Core.shiftIn (k n0 : Nat) (c : Core) : Core :=
  { c with live := c.live.shiftIn k n0,
           archive := c.archive.map (fun t => { t with site := t.site.shiftIn k n0 }) }

theorem wf_shiftIn (k n0 : Nat) (c : Core) : wf (c.shiftIn k n0) = wf c := by
  unfold Core.shiftIn
  cases ha : c.archive with
  | none => simp [wf, Core.archiveSite, ha]
  | some t => simp [wf, Core.archiveSite, ha, wfPair, Site.shiftIn_doc]

theorem skel_shiftIn (k n0 : Nat) (c : Core) : (c.shiftIn k n0).skel = c.skel := by
  unfold Core.shiftIn Core.skel
  cases c.archive <;> simp [Site.shiftIn_doc]

def Entity.shiftIn (k n0 : Nat) (e : Entity) : Entity :=
  ⟨e.val.shiftIn k n0, (wf_shiftIn k n0 e.val).trans e.property⟩

/-- Every entity of a store, transformed; the domain does not move. -/
def Store.mapEntities (s : Store) (f : Entity → Entity) : Store where
  get := fun j => (s.get j).map f
  dom := s.dom
  domSpec := by
    intro j
    rw [s.domSpec j]
    cases s.get j <;> rfl
  domNodup := s.domNodup

/-- `mapEntities`, compacted: `f` runs once per id when the store is built, not
once per lookup, and the store it hands on is one table (`Store.compact`,
Fast.lean). -/
def Store.mapEntitiesFast (s : Store) (f : Entity → Entity) : Store := (s.mapEntities f).compact

@[csimp] theorem Store.mapEntities_eq_mapEntitiesFast : @Store.mapEntities = @Store.mapEntitiesFast := by
  funext s f; exact (Store.compact_eq _).symm

def Doc.shiftFrom (n0 : Nat) (d : Doc) : Doc :=
  { d with prose := d.prose.map (fun q => (shiftRank n0 q.1, q.2)) }

/-- Shift document `k`'s ranks at or after `n0` up by one — its prose and every
placement in it, records and tombstones alike. -/
def PlanCore.shiftIn (k n0 : Nat) (p : PlanCore) : PlanCore :=
  { docs := p.docs.modify k (Doc.shiftFrom n0),
    store := p.store.mapEntities (Entity.shiftIn k n0) }

def WfPlan.shiftAt (p : WfPlan) (k n0 : Nat) : Except KErr WfPlan :=
  if h : planWf (p.val.shiftIn k n0) = true then .ok ⟨_, h⟩ else .error .badHorizon

/-- One past every rank document `k` uses: the end of the file. -/
def endRank (p : PlanCore) (k : DocIx) : Nat := (docRanks p k).foldl Nat.max 0 + 1

/-- The lowest rank of a live heading of `d` above `lo` satisfying `want`
(every rank, when `lo` is `none`). -/
def firstHeadingAbove (d : Doc) (lo : Option Nat) (want : List Char → Bool) : Option Nat :=
  d.prose.foldl (fun acc q =>
    if liveHeading d q && want q.2 &&
        (match lo with
         | none   => true
         | some l => decide (l < q.1)) then
      match acc with
      | none   => some q.1
      | some b => some (Nat.min b q.1)
    else acc) none

/-- Where in document `k` a line lands: `none` is the end of the file, `some n`
is "shift at `n` and take `n`" — the end of a section that another heading
follows.  `src` is the heading the line stood under in its own file. -/
def landingSpot (p : PlanCore) (k : DocIx) (l : Landing) (src : Option (List Char)) :
    Except KErr (Option Nat) :=
  match p.docs[k]? with
  | none   => .error .noTarget
  | some d =>
    match l with
    | .fileEnd        => .ok none
    | .demotedSection =>
      match firstHeadingAbove d none (fun h => secKind h == SecKind.demoted) with
      | none   => .error .noSection
      | some h => .ok (firstHeadingAbove d (some h) (fun _ => true))
    | .sameSection    =>
      match src with
      | none   => .ok (firstHeadingAbove d none (fun _ => true))
      | some s =>
        match firstHeadingAbove d none (fun h => headingBody h == headingBody s) with
        | none   => .error .noSection
        | some h => .ok (firstHeadingAbove d (some h) (fun _ => true))
    | .overdueSection =>
      match firstHeadingAbove d none (fun h => headingBody h == "Overdue".toList) with
      | none   => .error .noSection
      | some h => .ok (firstHeadingAbove d (some h) (fun _ => true))

/-- Relocate `i` into document `k` at the landing spot, through `f`. -/
def landAt (p : WfPlan) (k : DocIx) (spot : Option Nat) (i : Id)
    (f : Site → Entity → Except KErr Entity) : Except KErr WfPlan :=
  match spot with
  | none   => p.mapAt i (f ⟨k, endRank p.val k⟩)
  | some n =>
    match p.shiftAt k n with
    | .error x => .error x
    | .ok q    => q.mapAt i (f ⟨k, n⟩)

/-- The entity transform filing a line out of region `r` of grain `g`: the
table's disposition, through the command algebra's own transforms.  The copy is
`refile` — with the week row's child fold `x` floored into the record's estimate
(`refileX`) — so a line with a standing `# Demoted` record is merged into it (README
gap 53) rather than refused. -/
def fileE (g : Grain) (r : Region) (x : FoldFx) (t : Site) (e : Entity) : Except KErr Entity :=
  match (closePolicy g).disposition with
  | .move          => moveTo t e
  | .moveReopening => lift { e.val with live := t, status := reopen e.val.status,
                                        line := stampedLine (closeStamp g r.ix) e.val.skel }
  | .copy          =>
    match closeStamp g r.ix with
    | some st => refileX x t st e
    | none    => .error .badHorizon

/-- **A child dropped with its parent**: `[~]` in place — the fork point removed the
line from the week file (`remove_line_in`); the kernel removes no entity, and §0's
"demotion, not deletion" keeps the line (README "Stage 4 final, step 4"). -/
def dropE (e : Entity) : Except KErr Entity :=
  .ok ⟨{ e.val with status := .settled .dropped }, e.property⟩

/-! ## A tombstone that is not a `# Demoted` record (stage-4 hardening, repair)

`refile` merges a line into its item's tombstone and deletes the tombstone's old
placement — right when the tombstone *is* the item's `# Demoted` record, as in
§4.3's pre-close pair.  Fork-point `archived_record` and `stale_archive_copy` read
a record only off an item **in a month file, in the `# Demoted` section**.  A
tombstone anywhere else — a `[-]` line left in an earlier week file, beside an
open line in a later week (a hand edit; `readopt` removes both lines) — is an
archive, not a record, and merging into it deletes a line from a closed week
without a word.  The kernel holds one tombstone per item, so it cannot keep that
line *and* file a fresh record; the close refuses the item by the name it had
before README gap 53 closed, `alreadyDemoted`, and writes nothing. -/

/-- The item carries a tombstone that is not its `# Demoted` record. -/
def hasAStrayTomb (p : PlanCore) (e : Entity) : Bool :=
  match e.val.archive with
  | none   => false
  | some t => !demotedRecordPlacement p t.site

/-- The week row's copy over an item with a stray tombstone: refused. -/
def copiesOverAStrayTomb (g : Grain) (p : PlanCore) (e : Entity) : Bool :=
  decide ((closePolicy g).disposition = .copy) && hasAStrayTomb p e

/-- The refusal, after the landing: a step whose landing is refused keeps that
refusal (`badHorizon` before `alreadyDemoted`), and one whose landing succeeds over
a stray tombstone is refused and its post-state dropped. -/
def guardStray (b : Bool) (x : Except KErr WfPlan) : Except KErr WfPlan :=
  match x with
  | .error y => .error y
  | .ok q    => if b then .error .alreadyDemoted else .ok q

theorem guardStray_ok {b : Bool} {x : Except KErr WfPlan} {q : WfPlan}
    (h : guardStray b x = .ok q) : x = .ok q ∧ b = false := by
  unfold guardStray at h
  cases x with
  | error y => simp at h
  | ok q' => cases b <;> simp_all

theorem guardStray_error {b : Bool} {x : Except KErr WfPlan} {y : KErr}
    (h : guardStray b x = .error y) :
    x = .error y ∨ (y = .alreadyDemoted ∧ b = true ∧ ∃ q, x = .ok q) := by
  unfold guardStray at h
  cases x with
  | error y' => simp at h; exact Or.inl (by rw [h])
  | ok q' => cases b <;> simp_all

theorem guardStray_of_error {b : Bool} {x : Except KErr WfPlan} {y : KErr}
    (h : x = .error y) : guardStray b x = .error y := by
  subst h; rfl

theorem guardStray_false (x : Except KErr WfPlan) : guardStray false x = x := by
  cases x <;> rfl

/-! ## `close` -/

/-- **One step**: close id `i` of the plan it is handed, with what the week row's
child fold asks of it (`x`). -/
def closeOne (g : Grain) (now : Day) (x : FoldFx) (i : Id) : Transform := fun p =>
  match p.val.store.get i with
  | none   => .error .noSuchId
  | some e =>
    match closeAct g now p.val e.val.skel with
    | .stay   => .ok p
    | .carry  =>
      match carryTarget now p.val with
      | none   => .error .noTarget
      | some k => landAt p k none i moveTo
    | .file r =>
      if x.isDrop then p.mapAt i dropE
      else match closeTarget g now p.val with
      | none   => .error .noTarget
      | some k =>
        match landingSpot p.val k (closePolicy g).landing (sectionAt p.val e.val.live) with
        | .error x => .error x
        | .ok spot => guardStray (copiesOverAStrayTomb g p.val e) (landAt p k spot i (fileE g r x))
    | .overdue =>
      match overdueTarget p.val with
      | none   => .error .noTarget
      | some k =>
        match landingSpot p.val k .overdueSection (sectionAt p.val e.val.live) with
        | .error x => .error x
        | .ok spot => landAt p k spot i moveTo

/-- The ids a close of grain `g` at `now` acts on, in store order — which is
**not** file order: the loader builds `dom` in reverse, so folding this list
landed the lines it took in reverse of their source order (README gap 59). -/
def closeCandSet (g : Grain) (now : Day) (p : PlanCore) : List Id :=
  p.store.dom.filter (fun i =>
    match p.store.get i with
    | none   => false
    | some e =>
      match closeAct g now p e.val.skel with
      | .stay => false
      | _     => true)

/-! ### Source order (README gap 59)

A line landing at the end of a file, or at the end of a section, lands after
every line already there — so the fold must take the lines of one source file
in rank order for them to keep it.  The order is a structural insertion sort on
(document, rank): it reduces under `decide` (AGENTS §5.10), and `sortBySite_perm`
makes it a permutation, so every statement about *which* ids a close takes is
unchanged. -/

/-- Source order on placements: document, then rank. -/
def siteLe (a b : Site) : Bool :=
  decide (a.doc < b.doc) || (decide (a.doc = b.doc) && decide (a.rank ≤ b.rank))

theorem siteLe_iff (a b : Site) : siteLe a b = true ↔ a.doc < b.doc ∨ (a.doc = b.doc ∧ a.rank ≤ b.rank) := by
  simp [siteLe]

theorem siteLe_total (a b : Site) : siteLe a b = false → siteLe b a = true := by
  intro h
  have h' : ¬ (a.doc < b.doc ∨ (a.doc = b.doc ∧ a.rank ≤ b.rank)) := by
    rw [← siteLe_iff]; simp [h]
  rw [siteLe_iff]
  obtain ⟨d1, r1⟩ := a
  obtain ⟨d2, r2⟩ := b
  simp only at h' ⊢
  have h1 : ¬ (d1 < d2) := fun hc => h' (Or.inl hc)
  have h2 : ¬ (d1 = d2 ∧ r1 ≤ r2) := fun hc => h' (Or.inr hc)
  rcases Nat.lt_or_ge d2 d1 with hl | hl
  · exact Or.inl hl
  · have hd : d1 = d2 := Nat.le_antisymm hl (Nat.not_lt.1 h1)
    exact Or.inr ⟨hd.symm, Nat.le_of_lt (Nat.not_le.1 (fun hr => h2 ⟨hd, hr⟩))⟩

theorem siteLe_trans (a b c : Site) : siteLe a b = true → siteLe b c = true → siteLe a c = true := by
  simp only [siteLe_iff]
  obtain ⟨d1, r1⟩ := a
  obtain ⟨d2, r2⟩ := b
  obtain ⟨d3, r3⟩ := c
  simp only
  intro h1 h2
  rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
  · exact Or.inl (Nat.lt_trans h1 h2)
  · exact Or.inl h1
  · exact Or.inl h2
  · exact Or.inr ⟨rfl, Nat.le_trans h1 h2⟩

/-- The live placement an id has in plan `p` (`⟨0, 0⟩` for an id it lacks,
which no candidate is). -/
def liveSiteOf (p : PlanCore) (i : Id) : Site :=
  match p.store.get i with
  | none   => ⟨0, 0⟩
  | some e => e.val.live

def insertBySite (key : Id → Site) (x : Id) : List Id → List Id
  | []      => [x]
  | y :: ys => if siteLe (key x) (key y) then x :: y :: ys else y :: insertBySite key x ys

def sortBySite (key : Id → Site) : List Id → List Id
  | []      => []
  | x :: xs => insertBySite key x (sortBySite key xs)

theorem insertBySite_perm (key : Id → Site) (x : Id) :
    ∀ l : List Id, List.Perm (insertBySite key x l) (x :: l) := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    unfold insertBySite
    split
    · exact List.Perm.refl _
    · exact ((List.Perm.cons y ih).trans (List.Perm.swap x y ys))

theorem sortBySite_perm (key : Id → Site) : ∀ l : List Id, List.Perm (sortBySite key l) l := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih => exact (insertBySite_perm key x _).trans (List.Perm.cons x ih)

theorem insertBySite_sorted (key : Id → Site) (x : Id) :
    ∀ l : List Id, l.Pairwise (fun a b => siteLe (key a) (key b) = true) →
      (insertBySite key x l).Pairwise (fun a b => siteLe (key a) (key b) = true) := by
  intro l
  induction l with
  | nil => intro _; exact List.pairwise_singleton _ _
  | cons y ys ih =>
    intro h
    have hy := List.pairwise_cons.1 h
    unfold insertBySite
    split
    · rename_i hxy
      refine List.pairwise_cons.2 ⟨fun z hz => ?_, h⟩
      rcases List.mem_cons.1 hz with hz | hz
      · rw [hz]; exact hxy
      · exact siteLe_trans _ _ _ hxy (hy.1 z hz)
    · rename_i hxy
      have hyx := siteLe_total _ _ (by simpa using hxy)
      refine List.pairwise_cons.2 ⟨fun z hz => ?_, ih hy.2⟩
      rcases List.mem_cons.1 ((insertBySite_perm key x ys).mem_iff.1 hz) with hz | hz
      · rw [hz]; exact hyx
      · exact hy.1 z hz

theorem sortBySite_sorted (key : Id → Site) :
    ∀ l : List Id, (sortBySite key l).Pairwise (fun a b => siteLe (key a) (key b) = true) := by
  intro l
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x xs ih => exact insertBySite_sorted key x _ ih
/-- The ids a close of grain `g` at `now` acts on, **in source order**: by
document, then by rank. -/
def closeCands (g : Grain) (now : Day) (p : PlanCore) : List Id :=
  sortBySite (liveSiteOf p) (closeCandSet g now p)

theorem closeCands_perm (g : Grain) (now : Day) (p : PlanCore) :
    List.Perm (closeCands g now p) (closeCandSet g now p) :=
  sortBySite_perm _ _

theorem closeCands_sorted (g : Grain) (now : Day) (p : PlanCore) :
    (closeCands g now p).Pairwise (fun a b => siteLe (liveSiteOf p a) (liveSiteOf p b) = true) :=
  sortBySite_sorted _ _

/-! ### The week row's child fold (goal B3's repair, stage 4 final step 4)

Which lines count is fork-point `close_week`'s `demoted_ancestor`, read off the plan
the close is handed: a line the close **files** (`closeAct … = .file _`) whose
`@parent` is another line it files **from the same file** is a child, and it is
dropped; its minutes go to the nearest ancestor up that chain that is not itself
such a child — the root the close files forward.  A child that stays (an overdue
line filed to the backlog, a carried wall, a line of another file) is never folded,
and a line whose parent stays is filed as a root.  The chain is walked with the
store's size as fuel; `planWf`'s `parentsAcyclic` means the fuel never runs out,
and where it would, the line is filed as a root rather than dropped
(`dropsInto_spec`), so no minutes can vanish on a cycle the checker missed. -/

/-- The close files this line forward (or drops it): its action is `file`. -/
def filesLine (g : Grain) (now : Day) (p : PlanCore) (s : Skel) : Bool :=
  match closeAct g now p s with
  | .file _ => true
  | _       => false

/-- `j`'s parent, when the row drops children and the close files both from one file.
A line the close does not file is not read further (so a close of another grain,
which leaves every such line alone, cannot change the answer: `foldFxOf_congr`). -/
def foldParent (g : Grain) (now : Day) (p : PlanCore) (j : Id) : Option Id :=
  if (closePolicy g).children = .asAnyLine then none
  else match p.store.get j with
    | none    => none
    | some ej =>
      if filesLine g now p ej.val.skel then
        match ej.val.parent with
        | none   => none
        | some i =>
          match p.store.get i with
          | none    => none
          | some ei =>
            if filesLine g now p ei.val.skel && decide (ei.val.live.doc = ej.val.live.doc) then some i
            else none
      else none

/-- `foldParent`, reading the `@parent` before the action: a line with no parent — every
line of a tree with no hierarchy — is answered without classifying its placement, so
the week close's fold over the store costs one parent read per line (the fast twin;
`foldParent_eq_foldParentFast`). -/
def foldParentFast (g : Grain) (now : Day) (p : PlanCore) (j : Id) : Option Id :=
  if (closePolicy g).children = .asAnyLine then none
  else match p.store.get j with
    | none    => none
    | some ej =>
      match ej.val.parent with
      | none   => none
      | some i =>
        if filesLine g now p ej.val.skel then
          match p.store.get i with
          | none    => none
          | some ei =>
            if filesLine g now p ei.val.skel && decide (ei.val.live.doc = ej.val.live.doc) then some i
            else none
        else none

@[csimp] theorem foldParent_eq_foldParentFast : @foldParent = @foldParentFast := by
  funext g now p j
  unfold foldParent foldParentFast
  split
  · rfl
  · cases p.store.get j with
    | none => rfl
    | some ej =>
      simp only
      cases ej.val.parent with
      | none => cases filesLine g now p ej.val.skel <;> rfl
      | some i => rfl

/-- Walk `foldParent` up from `j` to the first line that has none, within `n` links. -/
def foldUp (g : Grain) (now : Day) (p : PlanCore) : Nat → Id → Option Id
  | 0,     _ => none
  | n + 1, j =>
    match foldParent g now p j with
    | none   => some j
    | some i => foldUp g now p n i

/-- **The line a dropped child's minutes go to** — `none` for a line that is not
dropped. -/
def dropsInto (g : Grain) (now : Day) (p : PlanCore) (j : Id) : Option Id :=
  match foldParent g now p j with
  | none   => none
  | some i => foldUp g now p p.store.dom.length i

/-- A line's own remaining — fork-point `own_minutes`: its `est:`, else its leading
estimate, and `0` for a line with neither. -/
def ownMinutes (bm : Nat) (p : PlanCore) (j : Id) : Nat :=
  match p.store.get j with
  | none   => 0
  | some e => remainingOf bm e.val.line

/-- Every dropped line, with the line its minutes go to and its own minutes — each
dropped line once (the store's domain has no duplicates). -/
def foldTab (g : Grain) (now : Day) (bm : Nat) (p : PlanCore) : List (Id × Nat) :=
  p.store.dom.filterMap (fun j => (dropsInto g now p j).map (fun r => (r, ownMinutes bm p j)))

/-- `foldTab`, answering a row that drops no children without walking the store (the
fast twin; `foldTab_eq_foldTabFast`). -/
def foldTabFast (g : Grain) (now : Day) (bm : Nat) (p : PlanCore) : List (Id × Nat) :=
  if (closePolicy g).children = .asAnyLine then [] else foldTab g now bm p

def foldTabSum (t : List (Id × Nat)) (i : Id) : Nat :=
  t.foldl (fun a q => if q.1 = i then a + q.2 else a) 0

def foldTabHas (t : List (Id × Nat)) (i : Id) : Bool := t.any (fun q => decide (q.1 = i))

/-- **§6.4's `Σ own remaining of the children dropped with it`**, for the line `i`
their minutes go to. -/
def foldedMinutes (g : Grain) (now : Day) (bm : Nat) (p : PlanCore) (i : Id) : Nat :=
  foldTabSum (foldTab g now bm p) i

/-- What the fold asks of line `i`, read off a precomputed table. -/
def foldFxIn (t : List (Id × Nat)) (g : Grain) (now : Day) (bm : Nat) (p : PlanCore) (i : Id) : FoldFx :=
  match dropsInto g now p i with
  | some _ => .drop
  | none   => if foldTabHas t i then .lift bm (foldTabSum t i) else .none

/-- **What the week row's child fold asks of each line of `p`**: dropped, lifted by the
minutes of the children dropped into it, or nothing. -/
def foldFxOf (g : Grain) (now : Day) (bm : Nat) (p : PlanCore) (i : Id) : FoldFx :=
  foldFxIn (foldTab g now bm p) g now bm p i

/-- **§6.3's lifecycle at one grain**: fold `closeOne` over the candidates, each with
what the child fold asks of it, computed once from the plan the close is handed.
The provisional `Goals.close` signature, made real — the grain, the instant,
`Transform` as the shape, and `ClosePolicy` read from the table rather than
passed — and, since goal B3's repair, the block length, which the week row's fold
needs to add a `1b` child to a `30m` one (§4.1). -/
def close (g : Grain) (now : Day) (bm : Nat) : Transform := fun p =>
  let t := foldTab g now bm p.val
  (closeCands g now p.val).foldlM (fun q i => closeOne g now (foldFxIn t g now bm p.val i) i q) p

/-! ## What one step does

Every step keeps the files' kinds and regions (`Frame`), leaves every other
id's skeleton alone, and turns its own id's skeleton into `stepSkel` of it —
after which the id is not one a close of that grain would take again, because
the file it now sits in is `closeTo g now` or the live week, and neither is
closed (`closeTo_target_is_open`, `regionOf_is_open`). -/

theorem WfPlan.mapAt_spec {p q : WfPlan} {i : Id} {f : Entity → Except KErr Entity}
    (h : p.mapAt i f = .ok q) :
    q.val.docs = p.val.docs ∧ (∀ j, j ≠ i → q.val.store.get j = p.val.store.get j) ∧
      ∃ e e', p.val.store.get i = some e ∧ f e = .ok e' ∧ q.val.store.get i = some e' := by
  unfold WfPlan.mapAt at h
  split at h
  · simp at h
  · rename_i e hget
    split at h
    · simp at h
    · rename_i e' hf
      split at h
      · injection h with h
        subst h
        exact ⟨rfl, fun j hj => Store.get_set_other p.val.store i j e' (by rw [hget]; rfl) hj,
          e, e', hget, hf, Store.get_set_self p.val.store i e' (by rw [hget]; rfl)⟩
      · simp at h

theorem WfPlan.shiftAt_val {p q : WfPlan} {k n : Nat} (h : p.shiftAt k n = .ok q) :
    q.val = p.val.shiftIn k n := by
  unfold WfPlan.shiftAt at h
  split at h
  · injection h with h
    rw [← h]
  · simp at h

theorem frame_of_docs {p q : PlanCore} (h : q.docs = p.docs) : Frame p q :=
  ⟨by rw [h], fun k => by simp [docKindAt, h], fun k => by simp [docRegion, h]⟩

theorem frame_shiftIn (p : PlanCore) (k n : Nat) : Frame p (p.shiftIn k n) := by
  refine ⟨List.length_modify _ _ _, fun j => ?_, fun j => ?_⟩
  · unfold docKindAt PlanCore.shiftIn
    simp only [List.getElem?_modify]
    cases p.docs[j]? with
    | none => rfl
    | some d => simp only [Option.map_eq_map, Option.map_some]; split <;> rfl
  · unfold docRegion PlanCore.shiftIn
    simp only [List.getElem?_modify]
    cases p.docs[j]? with
    | none => rfl
    | some d => simp only [Option.map_eq_map, Option.map_some]; split <;> rfl

theorem landAt_spec {p q : WfPlan} {k : DocIx} {spot : Option Nat} {i : Id}
    {f : Site → Entity → Except KErr Entity} (h : landAt p k spot i f = .ok q) :
    Frame p.val q.val ∧
      (∀ j, j ≠ i → (q.val.store.get j).map (fun e => e.val.skel) =
        (p.val.store.get j).map (fun e => e.val.skel)) ∧
      ∃ e e' t f', p.val.store.get i = some e ∧ e'.val.skel = e.val.skel ∧ t.doc = k ∧
        f t e' = .ok f' ∧ q.val.store.get i = some f' := by
  cases spot with
  | none =>
    unfold landAt at h
    obtain ⟨hd, hj, e, e', hget, hf, hq⟩ := WfPlan.mapAt_spec h
    exact ⟨frame_of_docs hd, fun j hji => by rw [hj j hji], e, e, _, e', hget, rfl, rfl, hf, hq⟩
  | some n =>
    unfold landAt at h
    simp only at h
    cases h1 : p.shiftAt k n with
    | error x => simp [h1] at h
    | ok q1 =>
      simp only [h1] at h
      have hv := WfPlan.shiftAt_val h1
      obtain ⟨hd, hj, e1, e', hget1, hf, hq⟩ := WfPlan.mapAt_spec h
      have hfr : Frame p.val q.val := by
        have := frame_shiftIn p.val k n
        rw [← hv] at this
        exact this.trans (frame_of_docs hd)
      have hshift : ∀ j, q1.val.store.get j = (p.val.store.get j).map (Entity.shiftIn k n) := by
        intro j; rw [hv]; rfl
      refine ⟨hfr, fun j hji => ?_, ?_⟩
      · rw [hj j hji, hshift j]
        cases p.val.store.get j with
        | none => rfl
        | some x => simp only [Option.map_some]; exact congrArg some (skel_shiftIn k n x.val)
      · have hget1' := hshift i
        cases hpi : p.val.store.get i with
        | none => rw [hpi] at hget1'; rw [hget1'] at hget1; simp at hget1
        | some e =>
          rw [hpi] at hget1'
          rw [hget1'] at hget1
          simp only [Option.map_some, Option.some.injEq] at hget1
          subst hget1
          exact ⟨e, _, _, e', rfl, skel_shiftIn k n e.val, rfl, hf, hq⟩

theorem moveTo_skel {t : Site} {e f : Entity} (h : moveTo t e = .ok f) :
    f.val.skel = { e.val.skel with doc := t.doc } := by
  have hv := lift_roundtrips _ _ h
  rw [hv]
  rfl

theorem moveTo_live {t : Site} {e f : Entity} (h : moveTo t e = .ok f) : f.val.live = t := by
  have hv := lift_roundtrips _ _ h
  rw [hv]

theorem fileE_skel {g : Grain} {r : Region} {x : FoldFx} {t : Site} {e f : Entity}
    (h : fileE g r x t e = .ok f) : f.val.skel = skelAfter g r t.doc x e.val.skel ∧ f.val.live = t := by
  unfold fileE at h
  unfold skelAfter
  cases hd : (closePolicy g).disposition with
  | move =>
    simp only [hd] at h ⊢
    exact ⟨moveTo_skel h, moveTo_live h⟩
  | moveReopening =>
    simp only [hd] at h ⊢
    have hv := lift_roundtrips _ _ h
    rw [hv]
    exact ⟨rfl, rfl⟩
  | copy =>
    simp only [hd] at h ⊢
    cases hs : closeStamp g r.ix with
    | none => simp [hs] at h
    | some st =>
      simp only [hs] at h ⊢
      have hv := refileX_roundtrips _ _ _ _ _ h
      rw [hv]
      exact ⟨rfl, rfl⟩

theorem closedRegionOf_frame {p q : PlanCore} (hf : Frame p q) (g : Grain) (now : Day) (k : DocIx) :
    closedRegionOf g now q k = closedRegionOf g now p k := by
  unfold closedRegionOf
  rw [hf.2.2 k, hf.2.1 k]

theorem closeAct_frame {p q : PlanCore} (hf : Frame p q) (g : Grain) (now : Day) (s : Skel) :
    closeAct g now q s = closeAct g now p s := by
  unfold closeAct
  rw [closedRegionOf_frame hf]

theorem findDocIx_frame {p q : PlanCore} (hf : Frame p q) (kind : DocKind) (r : Region) :
    findDocIx q kind r = findDocIx p kind r := by
  unfold findDocIx
  rw [hf.1]
  simp only [hf.2.1, hf.2.2]

theorem overdueTarget_frame {p q : PlanCore} (hf : Frame p q) : overdueTarget q = overdueTarget p := by
  unfold overdueTarget
  rw [hf.1]
  simp only [hf.2.1, hf.2.2]

theorem stepSkel_frame {p q : PlanCore} (hf : Frame p q) (g : Grain) (now : Day) (x : FoldFx) (s : Skel) :
    stepSkel g now q x s = stepSkel g now p x s := by
  unfold stepSkel carryTarget closeTarget
  rw [closeAct_frame hf, findDocIx_frame hf, findDocIx_frame hf, overdueTarget_frame hf]

theorem findDocIx_spec {p : PlanCore} {kind : DocKind} {r : Region} {k : DocIx}
    (h : findDocIx p kind r = some k) :
    k < p.docs.length ∧ docKindAt p k = kind ∧ docRegion p k = some r := by
  unfold findDocIx at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨List.mem_range.1 hm, hp.1, hp.2⟩

theorem overdueTarget_spec {p : PlanCore} {k : DocIx} (h : overdueTarget p = some k) :
    k < p.docs.length ∧ docKindAt p k = .backlog ∧ docRegion p k = none := by
  unfold overdueTarget at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨List.mem_range.1 hm, hp.1, hp.2⟩

/-- **A line in a file with no region is not one any close takes** — the
backlog, where D7's route files a line, above all: so what a close moved there is
never taken again (L16's argument for the fourth action). -/
theorem closeAct_of_regionless {p : PlanCore} {g : Grain} {now : Day} {s : Skel}
    (hr : docRegion p s.doc = none) : closeAct g now p s = .stay := by
  unfold closeAct closedRegionOf
  rw [hr]

/-- A line in a file whose region is open is not one any close takes. -/
theorem closeAct_of_open {p : PlanCore} {g : Grain} {now : Day} {s : Skel} {r : Region}
    (hr : docRegion p s.doc = some r) (ho : ¬ Closed r now) : closeAct g now p s = .stay := by
  unfold closeAct closedRegionOf
  rw [hr]
  simp [ho]

/-- A line whose box the row does not take is not one the close takes — a settled
line above all, and so a child the fold dropped. -/
theorem closeAct_of_takes_false {p : PlanCore} {g : Grain} {now : Day} {s : Skel}
    (h : (closePolicy g).takes s.status = false) : closeAct g now p s = .stay := by
  unfold closeAct
  split
  · rfl
  · rw [if_pos h]

theorem closeAct_of_settled (p : PlanCore) (g : Grain) (now : Day) (s : Skel) (o : Outcome) :
    closeAct g now p { s with status := .settled o } = .stay :=
  closeAct_of_takes_false (close_never_takes_a_settled_line g o)

/-- A line the fold drops becomes `[~]`, and nothing else about it changes. -/
theorem stepSkel_of_drop {g : Grain} {now : Day} {p : PlanCore} {x : FoldFx} {s : Skel} {r : Region}
    (hact : closeAct g now p s = .file r) (hx : x.isDrop = true) :
    stepSkel g now p x s = { s with status := .settled .dropped } := by
  simp only [stepSkel, hact, hx, ↓reduceIte]

/-- A filed line the fold does not drop is filed as the table's row says. -/
theorem stepSkel_of_file {g : Grain} {now : Day} {p : PlanCore} {x : FoldFx} {s : Skel} {r : Region}
    (hact : closeAct g now p s = .file r) (hx : x.isDrop = false) :
    stepSkel g now p x s = match closeTarget g now p with
      | some k => skelAfter g r k x s
      | none   => s := by
  simp only [stepSkel, hact, hx, Bool.false_eq_true, ↓reduceIte]

theorem dropE_skel {e f : Entity} (h : dropE e = .ok f) :
    f.val.skel = { e.val.skel with status := .settled .dropped } ∧ f.val.live = e.val.live := by
  unfold dropE at h
  injection h with h
  subst h
  exact ⟨rfl, rfl⟩

theorem closeOne_spec {g : Grain} {now : Day} {x : FoldFx} {i : Id} {p q : WfPlan}
    (h : closeOne g now x i p = .ok q) :
    Frame p.val q.val ∧
      (∀ j, j ≠ i → (q.val.store.get j).map (fun e => e.val.skel) =
        (p.val.store.get j).map (fun e => e.val.skel)) ∧
      ∃ e f, p.val.store.get i = some e ∧ q.val.store.get i = some f ∧
        f.val.skel = stepSkel g now p.val x e.val.skel ∧ closeAct g now p.val f.val.skel = .stay := by
  unfold closeOne at h
  split at h
  · simp at h
  · rename_i e hget
    split at h
    · rename_i hact
      injection h with h
      subst h
      exact ⟨Frame.refl _, fun _ _ => rfl, e, e, hget, hget, by unfold stepSkel; rw [hact], hact⟩
    · rename_i hact
      split at h
      · simp at h
      · rename_i k hk
        obtain ⟨hfr, hj, e0, e', t, f', hget0, hsk, htd, hmv, hq⟩ := landAt_spec h
        rw [hget] at hget0
        injection hget0 with hget0
        subst hget0
        have hfs := moveTo_skel hmv
        refine ⟨hfr, hj, e, f', hget, hq, ?_, ?_⟩
        · rw [hfs, hsk, htd]
          unfold stepSkel
          rw [hact, hk]
        · obtain ⟨_, _, hreg⟩ := findDocIx_spec hk
          refine closeAct_of_open (r := regionOf week now) ?_ (regionOf_is_open week now)
          rw [hfs]
          simp only
          rw [htd]
          exact hreg
    · rename_i r hact
      split at h
      · rename_i hx
        obtain ⟨hd, hj, e0, f', hget0, hdrop, hq⟩ := WfPlan.mapAt_spec h
        rw [hget] at hget0
        injection hget0 with hget0
        subst hget0
        obtain ⟨hfs, _⟩ := dropE_skel hdrop
        refine ⟨frame_of_docs hd, fun j hji => by rw [hj j hji], e, f', hget, hq, ?_, ?_⟩
        · rw [hfs, stepSkel_of_drop hact hx]
        · rw [hfs]
          exact closeAct_of_settled _ _ _ _ _
      · rename_i hx
        split at h
        · simp at h
        · rename_i k hk
          split at h
          · simp at h
          · rename_i spot _
            obtain ⟨hfr, hj, e0, e', t, f', hget0, hsk, htd, hfe, hq⟩ := landAt_spec (guardStray_ok h).1
            rw [hget] at hget0
            injection hget0 with hget0
            subst hget0
            obtain ⟨hfs, hlive⟩ := fileE_skel hfe
            refine ⟨hfr, hj, e, f', hget, hq, ?_, ?_⟩
            · rw [hfs, hsk, htd, stepSkel_of_file hact (by simpa using hx), hk]
            · obtain ⟨_, _, hreg⟩ := findDocIx_spec hk
              refine closeAct_of_open (r := closeTo g now) ?_ (closeTo_target_is_open g now)
              show docRegion p.val f'.val.live.doc = _
              rw [hlive, htd]
              exact hreg
    · rename_i hact
      split at h
      · simp at h
      · rename_i k hk
        split at h
        · simp at h
        · obtain ⟨hfr, hj, e0, e', t, f', hget0, hsk, htd, hmv, hq⟩ := landAt_spec h
          rw [hget] at hget0
          injection hget0 with hget0
          subst hget0
          have hfs := moveTo_skel hmv
          refine ⟨hfr, hj, e, f', hget, hq, ?_, ?_⟩
          · rw [hfs, hsk, htd]
            unfold stepSkel
            rw [hact, hk]
          · obtain ⟨_, _, hreg⟩ := overdueTarget_spec hk
            refine closeAct_of_regionless ?_
            rw [hfs]
            simp only
            rw [htd]
            exact hreg

/-! ## The fold -/

theorem foldlM_closeOne_spec (g : Grain) (now : Day) (fx : Id → FoldFx) (p0 : WfPlan) :
    ∀ (l : List Id) (p q : WfPlan) (done : List Id),
      l.Nodup → (∀ i ∈ l, i ∉ done) → Frame p0.val p.val →
      (∀ j, j ∉ done → (p.val.store.get j).map (fun e => e.val.skel) =
        (p0.val.store.get j).map (fun e => e.val.skel)) →
      (∀ j, j ∈ done → ∃ e f, p0.val.store.get j = some e ∧ p.val.store.get j = some f ∧
        f.val.skel = stepSkel g now p0.val (fx j) e.val.skel ∧
        closeAct g now p0.val f.val.skel = .stay) →
      l.foldlM (fun q i => closeOne g now (fx i) i q) p = .ok q →
      Frame p0.val q.val ∧
        (∀ j, j ∉ done → j ∉ l → (q.val.store.get j).map (fun e => e.val.skel) =
          (p0.val.store.get j).map (fun e => e.val.skel)) ∧
        (∀ j, j ∈ done ∨ j ∈ l → ∃ e f, p0.val.store.get j = some e ∧
          q.val.store.get j = some f ∧ f.val.skel = stepSkel g now p0.val (fx j) e.val.skel ∧
          closeAct g now p0.val f.val.skel = .stay) := by
  intro l
  induction l with
  | nil =>
    intro p q done _ _ hfr hun hdone h
    simp only [List.foldlM_nil] at h
    injection h with h
    subst h
    exact ⟨hfr, fun j hj _ => hun j hj, fun j hj => by simp at hj; exact hdone j hj⟩
  | cons i rest ih =>
    intro p q done hnd hdis hfr hun hdone h
    simp only [List.foldlM_cons] at h
    cases h1 : closeOne g now (fx i) i p with
    | error x => rw [h1] at h; simp [bind, Except.bind] at h
    | ok p1 =>
      rw [h1] at h
      simp only [bind, Except.bind] at h
      obtain ⟨hf1, hj1, e, f, hpe, hp1f, hsk, hst⟩ := closeOne_spec h1
      have hnd' := List.nodup_cons.1 hnd
      have hi : i ∉ done := hdis i (List.mem_cons_self ..)
      have hfr1 : Frame p0.val p1.val := hfr.trans hf1
      -- the id this step closed, seen from `p0`
      have hpi := hun i hi
      rw [hpe] at hpi
      cases hp0 : p0.val.store.get i with
      | none => rw [hp0] at hpi; simp at hpi
      | some e0 =>
        rw [hp0] at hpi
        simp only [Option.map_some, Option.some.injEq] at hpi
        have ih' := ih p1 q (i :: done) hnd'.2
          (fun x hx hmem => by
            rcases List.mem_cons.1 hmem with rfl | hmem
            · exact hnd'.1 hx
            · exact hdis x (List.mem_cons_of_mem _ hx) hmem)
          hfr1
          (fun j hj => by
            have hji : j ≠ i := fun hc => hj (by rw [hc]; exact List.mem_cons_self ..)
            have hjd : j ∉ done := fun hc => hj (List.mem_cons_of_mem _ hc)
            rw [hj1 j hji, hun j hjd])
          (fun j hj => by
            rcases List.mem_cons.1 hj with rfl | hjd
            · refine ⟨e0, f, hp0, hp1f, ?_, ?_⟩
              · rw [hsk, stepSkel_frame hfr, hpi]
              · rw [← closeAct_frame hfr]; exact hst
            · obtain ⟨a, b, ha, hb, hab, hc⟩ := hdone j hjd
              have hji : j ≠ i := fun hc => hi (by rw [← hc]; exact hjd)
              have hm := hj1 j hji
              rw [hb] at hm
              cases hp1j : p1.val.store.get j with
              | none => rw [hp1j] at hm; simp at hm
              | some b1 =>
                rw [hp1j] at hm
                simp only [Option.map_some, Option.some.injEq] at hm
                exact ⟨a, b1, ha, rfl, by rw [hm, hab], by rw [hm]; exact hc⟩)
          h
        refine ⟨ih'.1, fun j hj hjl => ?_, fun j hj => ?_⟩
        · refine ih'.2.1 j ?_ (fun hc => hjl (List.mem_cons_of_mem _ hc))
          intro hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact hjl (List.mem_cons_self ..)
          · exact hj hc
        · refine ih'.2.2 j ?_
          rcases hj with hj | hj
          · exact Or.inl (List.mem_cons_of_mem _ hj)
          · rcases List.mem_cons.1 hj with rfl | hj
            · exact Or.inl (List.mem_cons_self ..)
            · exact Or.inr hj

theorem closeCands_nodup (g : Grain) (now : Day) (p : PlanCore) : (closeCands g now p).Nodup :=
  (closeCands_perm g now p).nodup_iff.2 (p.store.domNodup.filter _)

theorem mem_closeCands_iff {g : Grain} {now : Day} {p : PlanCore} {i : Id} :
    i ∈ closeCands g now p ↔ i ∈ closeCandSet g now p :=
  (closeCands_perm g now p).mem_iff

theorem closeAct_of_not_mem_closeCands {g : Grain} {now : Day} {p : PlanCore} {j : Id} {e : Entity}
    (hj : j ∉ closeCands g now p) (hget : p.store.get j = some e) :
    closeAct g now p e.val.skel = .stay := by
  cases hact : closeAct g now p e.val.skel with
  | stay => rfl
  | carry =>
    exfalso; apply hj
    refine mem_closeCands_iff.2 <| List.mem_filter.2 ⟨(p.store.domSpec j).2 (by rw [hget]; rfl), ?_⟩
    rw [hget]; simp only [hact]
  | file r =>
    exfalso; apply hj
    refine mem_closeCands_iff.2 <| List.mem_filter.2 ⟨(p.store.domSpec j).2 (by rw [hget]; rfl), ?_⟩
    rw [hget]; simp only [hact]
  | overdue =>
    exfalso; apply hj
    refine mem_closeCands_iff.2 <| List.mem_filter.2 ⟨(p.store.domSpec j).2 (by rw [hget]; rfl), ?_⟩
    rw [hget]; simp only [hact]

/-- **The denotation of `close`.**  A successful close keeps every file's kind
and region, turns every id's skeleton into `stepSkel` of what it was, and leaves
no line that a close of the same grain at the same instant would take again. -/
theorem close_spec {g : Grain} {now : Day} {bm : Nat} {p q : WfPlan} (h : close g now bm p = .ok q) :
    Frame p.val q.val ∧
      ∀ j, (q.val.store.get j).map (fun e => e.val.skel) =
          (p.val.store.get j).map (fun e => stepSkel g now p.val (foldFxOf g now bm p.val j) e.val.skel) ∧
        ∀ f, q.val.store.get j = some f → closeAct g now q.val f.val.skel = .stay := by
  have hf := foldlM_closeOne_spec g now (foldFxOf g now bm p.val) p (closeCands g now p.val) p q []
    (closeCands_nodup g now p.val) (fun _ _ hc => by simp at hc) (Frame.refl _)
    (fun _ _ => rfl) (fun _ hj => by simp at hj) h
  obtain ⟨hfr, hun, hdone⟩ := hf
  refine ⟨hfr, fun j => ?_⟩
  by_cases hjc : j ∈ closeCands g now p.val
  · obtain ⟨e, f, he, hfq, hsk, hst⟩ := hdone j (Or.inr hjc)
    refine ⟨by rw [he, hfq]; simp [hsk], fun f' hf' => ?_⟩
    rw [hfq] at hf'
    injection hf' with hf'
    subst hf'
    rw [closeAct_frame hfr]
    exact hst
  · have hm := hun j (by simp) hjc
    cases hpj : p.val.store.get j with
    | none =>
      rw [hpj] at hm
      refine ⟨by rw [hm]; rfl, fun f hf => ?_⟩
      rw [hf] at hm; simp at hm
    | some e =>
      rw [hpj] at hm
      have hst := closeAct_of_not_mem_closeCands hjc hpj
      have hstep : stepSkel g now p.val (foldFxOf g now bm p.val j) e.val.skel = e.val.skel := by
        unfold stepSkel; rw [hst]
      refine ⟨by rw [hm]; simp [hstep], fun f hf => ?_⟩
      rw [hf] at hm
      simp only [Option.map_some, Option.some.injEq] at hm
      rw [closeAct_frame hfr, hm]
      exact hst

/-- **`close_skel`**: the per-id reading of `close_spec`, with both lookups
named. -/
theorem close_skel {g : Grain} {now : Day} {bm : Nat} {p q : WfPlan} (h : close g now bm p = .ok q)
    {i : Id} {e f : Entity} (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) :
    f.val.skel = stepSkel g now p.val (foldFxOf g now bm p.val i) e.val.skel := by
  have := ((close_spec h).2 i).1
  rw [hp, hq] at this
  simpa using this


/-! ## What a close guarantees, read off `close_spec` -/

theorem exemptAct_cases (x : Exemption) (b : Bool) :
    exemptAct x b = .stay ∨ exemptAct x b = .carry := by
  cases x <;> cases b <;> simp [exemptAct]

/-- **A recurring line and a wall are never *filed*.**  Whatever the table's
exemption column says, `exemptAct` has no `file` branch; and a wall that is over,
with `persist`, is moved undemoted to the backlog's `# Overdue` at the week row
(D7, fork-point `close_week`'s `overdue` before `carried_walls`).  (Restates
`closeAct_of_exempt`, whose `stay ∨ carry` that wall falsifies since D7.) -/
theorem closeAct_never_files_an_exempt_line {g : Grain} {now : Day} {p : PlanCore} {s : Skel}
    (hx : s.recurring = true ∨ ∃ b, s.wallAhead now = some b) :
    closeAct g now p s = .stay ∨ closeAct g now p s = .carry ∨ closeAct g now p s = .overdue := by
  unfold closeAct
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · split
      · rcases exemptAct_cases (closePolicy g).recurring true with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rename_i hrec
        split
        · exact Or.inr (Or.inr rfl)
        · rcases hx with hx | ⟨b, hb⟩
          · exact absurd hx hrec
          · rw [hb]
            rcases exemptAct_cases (closePolicy g).walls b with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)

/-! ### What the child fold asks, read back

`foldFxOf` is computed once from the plan a close is handed.  These lemmas say what
it computed: a dropped line is one the close files whose parent it files from the
same file (`foldParent_spec`); its minutes go to a line the close files from that
file and does not drop (`dropsInto_spec`); every such line's minutes are counted in
that line's `foldedMinutes` (`ownMinutes_le_foldedMinutes`); and a row that does not
drop children asks nothing of any line (`foldFxOf_of_asAnyLine`). -/

theorem foldParent_of_asAnyLine {g : Grain} {now : Day} {p : PlanCore} {j : Id}
    (h : (closePolicy g).children = .asAnyLine) : foldParent g now p j = none := by
  unfold foldParent; rw [if_pos h]

theorem dropsInto_of_asAnyLine {g : Grain} {now : Day} {p : PlanCore} {j : Id}
    (h : (closePolicy g).children = .asAnyLine) : dropsInto g now p j = none := by
  unfold dropsInto; rw [foldParent_of_asAnyLine h]

theorem foldTab_of_asAnyLine {g : Grain} {now : Day} {bm : Nat} {p : PlanCore}
    (h : (closePolicy g).children = .asAnyLine) : foldTab g now bm p = [] := by
  unfold foldTab
  rw [List.filterMap_eq_nil_iff]
  intro j _
  rw [dropsInto_of_asAnyLine h]
  rfl

@[csimp] theorem foldTab_eq_foldTabFast : @foldTab = @foldTabFast := by
  funext g now bm p
  unfold foldTabFast
  split
  · rename_i h; exact foldTab_of_asAnyLine h
  · rfl

/-- **A row that does not drop children asks nothing of any line.** -/
theorem foldFxOf_of_asAnyLine {g : Grain} {now : Day} {bm : Nat} {p : PlanCore} {i : Id}
    (h : (closePolicy g).children = .asAnyLine) : foldFxOf g now bm p i = .none := by
  unfold foldFxOf foldFxIn
  rw [dropsInto_of_asAnyLine h, foldTab_of_asAnyLine h]
  rfl

theorem children_of_not_copy {g : Grain} (h : (closePolicy g).disposition ≠ .copy) :
    (closePolicy g).children = .asAnyLine := by
  cases hc : (closePolicy g).children with
  | asAnyLine => rfl
  | dropIntoParent => exact absurd (closePolicy_drops_children_only_at_a_copying_row g hc) h

theorem closePolicy_children_cases (g : Grain) :
    (closePolicy g).children = .asAnyLine ∨ g = week := by
  match g with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr rfl
  | ⟨2, _⟩ => exact Or.inl rfl

theorem foldParent_spec {g : Grain} {now : Day} {p : PlanCore} {j i : Id}
    (h : foldParent g now p j = some i) :
    g = week ∧ ∃ ej ei, p.store.get j = some ej ∧ p.store.get i = some ei ∧ parentStep p j = some i ∧
      filesLine g now p ej.val.skel = true ∧ filesLine g now p ei.val.skel = true ∧
      ei.val.live.doc = ej.val.live.doc := by
  unfold foldParent at h
  split at h
  · simp at h
  · rename_i hc
    have hg : g = week := (closePolicy_children_cases g).resolve_left hc
    split at h
    · simp at h
    · rename_i ej hj
      split at h
      · rename_i hfj
        split at h
        · simp at h
        · rename_i i' hpar
          split at h
          · simp at h
          · rename_i ei hi
            split at h
            · rename_i hc2
              injection h with h
              subst h
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hc2
              refine ⟨hg, ej, ei, hj, hi, ?_, hfj, hc2.1, hc2.2⟩
              unfold parentStep
              rw [hj]
              exact hpar
            · simp at h
      · simp at h

theorem foldUp_spec {g : Grain} {now : Day} {p : PlanCore} :
    ∀ (n : Nat) (j r : Id), foldUp g now p n j = some r →
      foldParent g now p r = none ∧
        ∀ e, p.store.get j = some e → filesLine g now p e.val.skel = true →
          ∃ er, p.store.get r = some er ∧ filesLine g now p er.val.skel = true ∧
            er.val.live.doc = e.val.live.doc := by
  intro n
  induction n with
  | zero => intro j r h; simp [foldUp] at h
  | succ n ih =>
    intro j r h
    unfold foldUp at h
    split at h
    · rename_i hn
      injection h with h
      subst h
      exact ⟨hn, fun e he hf => ⟨e, he, hf, rfl⟩⟩
    · rename_i i hi
      obtain ⟨hn, hup⟩ := ih i r h
      refine ⟨hn, fun e he _ => ?_⟩
      obtain ⟨_, ej, ei, hj, hi', _, _, hfi, hdoc⟩ := foldParent_spec hi
      rw [he] at hj
      injection hj with hj
      subst hj
      obtain ⟨er, her, hfr, hdr⟩ := hup ei hi' hfi
      exact ⟨er, her, hfr, hdr.trans hdoc⟩

/-- **Where a dropped line's minutes go**: to a line of the same file that the close
files and does not itself drop — never into a line that vanishes with it. -/
theorem dropsInto_spec {g : Grain} {now : Day} {p : PlanCore} {j r : Id}
    (h : dropsInto g now p j = some r) :
    g = week ∧ r ≠ j ∧ dropsInto g now p r = none ∧
      ∃ ej er, p.store.get j = some ej ∧ p.store.get r = some er ∧
        filesLine g now p ej.val.skel = true ∧ filesLine g now p er.val.skel = true ∧
        er.val.live.doc = ej.val.live.doc := by
  unfold dropsInto at h
  split at h
  · simp at h
  · rename_i i hi
    obtain ⟨hg, ej, ei, hj, hi', _, hfj, hfi, hdoc⟩ := foldParent_spec hi
    obtain ⟨hn, hup⟩ := foldUp_spec _ i r h
    obtain ⟨er, her, hfr, hdr⟩ := hup ei hi' hfi
    refine ⟨hg, fun hc => ?_, by unfold dropsInto; rw [hn], ej, er, hj, her, hfj, hfr, hdr.trans hdoc⟩
    subst hc
    rw [hn] at hi
    cases hi

theorem foldTabSum_step (i : Id) (t : List (Id × Nat)) :
    ∀ a, t.foldl (fun a q => if q.1 = i then a + q.2 else a) a =
      a + t.foldl (fun a q => if q.1 = i then a + q.2 else a) 0 := by
  induction t with
  | nil => intro a; rfl
  | cons q t ih =>
    intro a
    simp only [List.foldl_cons]
    rw [ih, ih (if q.1 = i then 0 + q.2 else 0)]
    split <;> omega

theorem foldTabSum_of_not_has {t : List (Id × Nat)} {i : Id} (h : foldTabHas t i = false) :
    foldTabSum t i = 0 := by
  unfold foldTabSum
  unfold foldTabHas at h
  induction t with
  | nil => rfl
  | cons q t ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp only [List.foldl_cons, if_neg h.1]
    exact ih h.2

theorem le_foldTabSum {t : List (Id × Nat)} {i : Id} {n : Nat} (h : (i, n) ∈ t) : n ≤ foldTabSum t i := by
  unfold foldTabSum
  induction t with
  | nil => simp at h
  | cons q t ih =>
    simp only [List.foldl_cons]
    rw [foldTabSum_step]
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := ih h
      omega

theorem mem_foldTab {g : Grain} {now : Day} {bm : Nat} {p : PlanCore} {r : Id} {n : Nat}
    (h : (r, n) ∈ foldTab g now bm p) : ∃ j, dropsInto g now p j = some r ∧ n = ownMinutes bm p j := by
  unfold foldTab at h
  obtain ⟨j, _, hj⟩ := List.mem_filterMap.1 h
  cases hd : dropsInto g now p j with
  | none => rw [hd] at hj; cases hj
  | some r' =>
    rw [hd] at hj
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hj
    obtain ⟨rfl, rfl⟩ := hj
    exact ⟨j, hd, rfl⟩

/-- A dropped line has nothing folded into it: its own children's minutes went to
its root, past it. -/
theorem foldedMinutes_of_dropped {g : Grain} {now : Day} {bm : Nat} {p : PlanCore} {i r : Id}
    (h : dropsInto g now p i = some r) : foldedMinutes g now bm p i = 0 := by
  unfold foldedMinutes
  apply foldTabSum_of_not_has
  unfold foldTabHas
  rw [List.any_eq_false]
  intro q hq hc
  simp only [decide_eq_true_eq] at hc
  obtain ⟨j, hj, _⟩ := mem_foldTab (show (q.1, q.2) ∈ foldTab g now bm p from hq)
  rw [hc] at hj
  have h1 := (dropsInto_spec hj).2.2.1
  rw [h1] at h
  cases h

/-- **What the fold writes on a line is `foldEst` of the minutes folded into it** —
nothing for a line with nothing folded, a dropped line included. -/
theorem foldFxOf_apply (g : Grain) (now : Day) (bm : Nat) (p : PlanCore) (i : Id) (l : RawItem) :
    (foldFxOf g now bm p i).apply l = foldEst bm (foldedMinutes g now bm p i) l := by
  unfold foldFxOf foldFxIn
  cases hd : dropsInto g now p i with
  | some r =>
    rw [foldedMinutes_of_dropped hd, foldEst_zero]
    rfl
  | none =>
    simp only
    cases hh : foldTabHas (foldTab g now bm p) i with
    | true => rfl
    | false =>
      show l = _
      unfold foldedMinutes
      rw [foldTabSum_of_not_has hh, foldEst_zero]

theorem foldFxOf_isDrop (g : Grain) (now : Day) (bm : Nat) (p : PlanCore) (i : Id) :
    (foldFxOf g now bm p i).isDrop = (dropsInto g now p i).isSome := by
  unfold foldFxOf foldFxIn
  cases dropsInto g now p i with
  | some _ => rfl
  | none => simp only; split <;> rfl

theorem foldedMinutes_of_asAnyLine {g : Grain} {now : Day} {bm : Nat} {p : PlanCore} {i : Id}
    (h : (closePolicy g).children = .asAnyLine) : foldedMinutes g now bm p i = 0 := by
  unfold foldedMinutes
  rw [foldTab_of_asAnyLine h]
  rfl

/-- **Each dropped line's own remaining is counted in its root's.** -/
theorem ownMinutes_le_foldedMinutes {g : Grain} {now : Day} (bm : Nat) {p : PlanCore} {j r : Id}
    (h : dropsInto g now p j = some r) : ownMinutes bm p j ≤ foldedMinutes g now bm p r := by
  unfold foldedMinutes
  apply le_foldTabSum
  unfold foldTab
  refine List.mem_filterMap.2 ⟨j, ?_, by rw [h]; rfl⟩
  obtain ⟨_, _, _, ej, _, hj, _⟩ := dropsInto_spec h
  exact (p.store.domSpec j).2 (by rw [hj]; rfl)

theorem filesLine_iff {g : Grain} {now : Day} {p : PlanCore} {s : Skel} :
    filesLine g now p s = true ↔ ∃ r, closeAct g now p s = .file r := by
  unfold filesLine
  split <;> simp_all

/-! ### What a close guarantees, read off `close_spec` (continued) -/

/-- A step that does not file a line keeps its skeleton but for the file.  (Its
hypothesis gained the `overdue` action at D7; its statement gained the fold's
argument at B3's repair and is otherwise as before.) -/
theorem stepSkel_of_exempt {g : Grain} {now : Day} {p : PlanCore} {x : FoldFx} {s : Skel}
    (hx : closeAct g now p s = .stay ∨ closeAct g now p s = .carry ∨ closeAct g now p s = .overdue) :
    stepSkel g now p x s = { s with doc := (stepSkel g now p x s).doc } := by
  unfold stepSkel
  rcases hx with hx | hx | hx
  · rw [hx]
  · rw [hx]
    cases carryTarget now p <;> rfl
  · rw [hx]
    cases overdueTarget p <;> rfl

/-- Where `stepSkel` files a line, it names the line's new file — or it is the
unreachable copy-without-a-stamp branch and leaves the skeleton alone. -/
theorem skelAfter_doc (g : Grain) (r : Region) (k : DocIx) (x : FoldFx) (s : Skel) :
    (skelAfter g r k x s).doc = k ∨ skelAfter g r k x s = s := by
  unfold skelAfter
  cases (closePolicy g).disposition with
  | move => exact Or.inl rfl
  | moveReopening => exact Or.inl rfl
  | copy => cases closeStamp g r.ix <;> simp

/-- **Narrowed L18** (`close_leaves_no_live_line_in_a_closed_region`, which is
stated over every line and so over the `[x]` lines §6.3 leaves in an archive;
refuted as `close_leaves_live_lines_in_a_closed_region`, Boundary.lean).
After a close, no line is one the same close would take: every line still in a
closed region of grain `g` is settled — a child the fold dropped included —,
recurring, a wall, or of a box the row does not take. -/
theorem close_leaves_no_line_it_would_take {g : Grain} {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close g now bm p = .ok q) (i : Id) (f : Entity) (hq : q.val.store.get i = some f) :
    closeAct g now q.val f.val.skel = .stay :=
  ((close_spec h).2 i).2 f hq

/-- The same, unpacked into the goal's own shape, with the narrowing in the
hypotheses where a reader can see it: a line of the grain's own file kind, whose
box the row takes, that is neither recurring nor a wall, is not in a closed
region of that grain after the close. -/
theorem close_leaves_no_unfinished_line_in_a_closed_region {g : Grain} {now : Day} {bm : Nat}
    {p q : WfPlan} (h : close g now bm p = .ok q) (i : Id) (f : Entity)
    (hq : q.val.store.get i = some f) (r : Region)
    (hr : docRegion q.val f.val.live.doc = some r) (hg : r.grain = g)
    (hkind : docKindAt q.val f.val.live.doc = kindOfGrain g)
    (htakes : (closePolicy g).takes f.val.status = true)
    (hrec : f.val.recur = Recur.none) (hwall : ∀ a b : DT, f.val.shape ≠ Shape.interval a b) :
    ¬ Closed r now := by
  intro hc
  have hst := close_leaves_no_line_it_would_take h i f hq
  have hreg : closedRegionOf g now q.val f.val.skel.doc = some r := by
    show closedRegionOf g now q.val f.val.live.doc = some r
    unfold closedRegionOf
    rw [hr]
    simp [hkind, hg, hc]
  have hrec' : f.val.skel.recurring = false := by
    show decide (Field.viewRecur f.val.line ≠ Recur.none) = false
    have : Field.viewRecur f.val.line = Recur.none := hrec
    simp [this]
  have hwall' : f.val.skel.wallAhead now = none := by
    show (match Field.viewShape f.val.line with
          | .interval _ b => some (decide (now ≤ b.day))
          | _ => none) = none
    have hsh : ∀ a b : DT, Field.viewShape f.val.line ≠ Shape.interval a b := hwall
    cases hv : Field.viewShape f.val.line with
    | interval a b => exact absurd hv (hsh a b)
    | none => rfl
    | point _ => rfl
    | window _ _ => rfl
  have htakes' : (closePolicy g).takes f.val.skel.status = true := htakes
  unfold closeAct at hst
  rw [hreg] at hst
  simp only [htakes', hrec', hwall', Bool.true_eq_false, Bool.false_eq_true, if_false] at hst
  split at hst <;> simp at hst

theorem stepSkel_day_stamps (now : Day) (p : PlanCore) (x : FoldFx) (s : Skel) :
    (stepSkel day now p x s).stamps = s.stamps ∨
      ∃ n, (stepSkel day now p x s).stamps = s.stamps ++ [Stamp.day n] := by
  cases hact : closeAct day now p s with
  | stay => exact Or.inl (by unfold stepSkel; rw [hact])
  | carry => exact Or.inl (by unfold stepSkel; rw [hact]; cases carryTarget now p <;> rfl)
  | overdue => exact Or.inl (by unfold stepSkel; rw [hact]; cases overdueTarget p <;> rfl)
  | file r =>
    cases hx : x.isDrop with
    | true => exact Or.inl (by rw [stepSkel_of_drop hact hx]; rfl)
    | false =>
      rw [stepSkel_of_file hact hx]
      cases closeTarget day now p with
      | none => exact Or.inl rfl
      | some k =>
        refine Or.inr ⟨(Cal.ofDay r.ix).day, ?_⟩
        show (Field.viewDemoted (Field.setDemoted (s.stamps ++ [Stamp.day (Cal.ofDay r.ix).day])
          s.line)).getD [] = _
        rw [Field.view_set_demoted _ _ (by simp)]
        rfl

/-- **§6.3's day row stamps a day stamp** (discharged from `Goals.lean`).  A day
close that changes a line's stamps appends exactly one, and it is a `D` stamp —
so the month review's "≥ 2 stamps" cut list, which counts `W` stamps, cannot be
fed a day's leftovers as if they were a week's. -/
theorem close_day_stamps_a_day_stamp (now : Day) (bm : Nat) (p q : WfPlan)
    (h : close day now bm p = .ok q) (i : Id) (e f : Entity)
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f)
    (hchanged : f.val.stamps ≠ e.val.stamps) :
    ∃ n : Nat, f.val.stamps = e.val.stamps ++ [Stamp.day n] := by
  have hsk := close_skel h hp hq
  rcases stepSkel_day_stamps now p.val (foldFxOf day now bm p.val i) e.val.skel with hs | hs
  · exact absurd (by rw [← Core.skel_stamps, hsk, hs]; rfl) hchanged
  · obtain ⟨n, hn⟩ := hs
    exact ⟨n, by rw [← Core.skel_stamps, hsk, hn]; rfl⟩

/-- A step rewrites a line's bytes in one of three ways, or not at all: it sets
`demoted:`; or — the week row's copy — it sets `demoted:` over the line with the
child fold's estimate applied (`x.apply`); or, filing a line whose item already has a
`# Demoted` record (README gap 53), over the record's estimate carried and then the
fold applied.  (Restates `stepSkel_line_is_stamped_or_merged`, whose disjuncts a
record the fold lifted falsifies.) -/
theorem stepSkel_line_is_stamped_merged_or_folded (g : Grain) (now : Day) (p : PlanCore)
    (x : FoldFx) (s : Skel) :
    (stepSkel g now p x s).line = s.line ∨
      ((closePolicy g).disposition = .moveReopening ∧
        ∃ ss, (stepSkel g now p x s).line = Field.setDemoted ss s.line) ∨
      (∃ ss, (stepSkel g now p x s).line = Field.setDemoted ss (x.apply s.line)) ∨
      ∃ ss tl, s.archLine = some tl ∧
        (stepSkel g now p x s).line = Field.setDemoted ss (x.apply (carryEst tl s.line)) := by
  cases hact : closeAct g now p s with
  | stay => exact Or.inl (by unfold stepSkel; rw [hact])
  | carry => exact Or.inl (by unfold stepSkel; rw [hact]; cases carryTarget now p <;> rfl)
  | overdue => exact Or.inl (by unfold stepSkel; rw [hact]; cases overdueTarget p <;> rfl)
  | file r =>
    cases hx : x.isDrop with
    | true => exact Or.inl (by rw [stepSkel_of_drop hact hx])
    | false =>
      rw [stepSkel_of_file hact hx]
      cases closeTarget g now p with
      | none => exact Or.inl rfl
      | some k =>
        simp only
        unfold skelAfter
        cases hd : (closePolicy g).disposition with
        | move => exact Or.inl rfl
        | moveReopening =>
          simp only
          unfold stampedLine
          cases closeStamp g r.ix with
          | none => exact Or.inl rfl
          | some st => exact Or.inr (Or.inl ⟨by first | rfl | trivial | simp [hd], _, rfl⟩)
        | copy =>
          cases closeStamp g r.ix with
          | none => exact Or.inl rfl
          | some st =>
            cases s.archLine with
            | none => exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
            | some tl => exact Or.inr (Or.inr (Or.inr ⟨_, tl, rfl, rfl⟩))

/-- **Narrowed B1–B3, with gap 53's merge and B3's fold** (restates
`close_rewrites_a_line_only_by_stamping_or_merging_it`, whose three disjuncts a
record the child fold lifted falsifies — `a_folded_record_is_rewritten_beyond_its_stamp`,
Boundary.lean; that theorem restated `close_rewrites_a_line_only_by_stamping_it`,
whose two disjuncts a merged record falsifies, and B1–B3's
`close_writes_every_estimate_through_demoteEst` is refuted as
`close_writes_a_line_demoteEst_does_not`).  A close rewrites a line's bytes in these
ways only: it sets the `demoted:` token over the line with the child fold's estimate
(`foldEst` of the minutes of the children dropped with it, which writes nothing when
there are none or when the line covers them); or, filing a line whose item already
has a `# Demoted` record, over that record's estimate carried onto the line
(`carryEst`) and then the fold.  A dropped child's bytes do not change. -/
theorem close_rewrites_a_line_only_by_stamping_merging_or_folding_it {g : Grain} {now : Day} {bm : Nat}
    {p q : WfPlan} (h : close g now bm p = .ok q) (i : Id) (e f : Entity)
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) :
    f.val.line = e.val.line ∨
      (∃ ss, f.val.line = Field.setDemoted ss (foldEst bm (foldedMinutes g now bm p.val i) e.val.line)) ∨
      ∃ ss t, e.val.archive = some t ∧
        f.val.line = Field.setDemoted ss (foldEst bm (foldedMinutes g now bm p.val i) (carryEst t.line e.val.line)) := by
  have hsk := close_skel h hp hq
  have := stepSkel_line_is_stamped_merged_or_folded g now p.val (foldFxOf g now bm p.val i) e.val.skel
  rw [← hsk] at this
  simp only [foldFxOf_apply] at this
  rcases this with h1 | ⟨hd, ss, h2⟩ | h3 | ⟨ss, tl, ha, hl⟩
  · exact Or.inl h1
  · -- only the day row stamps without the fold, and it folds nothing
    refine Or.inr (Or.inl ⟨ss, ?_⟩)
    show f.val.skel.line = _
    rw [h2, foldedMinutes_of_asAnyLine (children_of_not_copy (by rw [hd]; decide)), foldEst_zero]
    rfl
  · exact Or.inr (Or.inl h3)
  · refine Or.inr (Or.inr ?_)
    cases he : e.val.archive with
    | none => simp [Core.skel, he] at ha
    | some t =>
      have ht : t.line = tl := by simpa [Core.skel, he] using ha
      exact ⟨ss, t, rfl, by rw [ht]; exact hl⟩

/-- **The old law, where it still holds as stated**, restated for the fold: a line
whose item has no standing record is rewritten only by its stamp, over the child
fold's estimate.  (Restates `close_rewrites_a_line_with_no_record_only_by_stamping_it`,
false of a record the fold lifted.) -/
theorem close_rewrites_a_line_with_no_record_only_by_stamping_or_folding_it {g : Grain} {now : Day}
    {bm : Nat} {p q : WfPlan} (h : close g now bm p = .ok q) (i : Id) (e f : Entity)
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f)
    (hrec : e.val.archive = none) :
    f.val.line = e.val.line ∨
      ∃ ss, f.val.line = Field.setDemoted ss (foldEst bm (foldedMinutes g now bm p.val i) e.val.line) := by
  rcases close_rewrites_a_line_only_by_stamping_merging_or_folding_it h i e f hp hq with h1 | h2 | ⟨_, t, ha, _⟩
  · exact Or.inl h1
  · exact Or.inr h2
  · rw [hrec] at ha; cases ha

/-- **The old law, where nothing is folded**: a line whose item has no standing
record and into which no child was dropped is rewritten only by its stamp. -/
theorem close_rewrites_a_line_with_no_record_and_nothing_folded_only_by_stamping_it {g : Grain}
    {now : Day} {bm : Nat} {p q : WfPlan} (h : close g now bm p = .ok q) (i : Id) (e f : Entity)
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f)
    (hrec : e.val.archive = none) (hfold : foldedMinutes g now bm p.val i = 0) :
    f.val.line = e.val.line ∨ ∃ ss, f.val.line = Field.setDemoted ss e.val.line := by
  rcases close_rewrites_a_line_with_no_record_only_by_stamping_or_folding_it h i e f hp hq hrec with h1 | ⟨ss, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨ss, by rw [h2, hfold, foldEst_zero]⟩

/-- **The estimate half of narrowed B1–B3, with gap 53's merge and B3's fold**
(restates `close_reads_every_remaining_estimate_through_demoteEst`, false of a record
the fold lifted: `a_folded_record_changes_a_remaining_estimate`, Boundary.lean).  At
the block length the close was run with, a close either leaves a line's remaining
estimate as it was, or gives it §6.4's `max` of what it read before — its own
reading, or, merging the line into its item's standing record, the reading
`demoteEst` writes with `userSet := ownsEstimate` of the line and `rec :=
recordedEst` of the record (L15) — and the minutes of the children dropped with it. -/
theorem close_reads_every_remaining_estimate_through_demoteEst_and_the_fold {g : Grain} {now : Day}
    {bm : Nat} {p q : WfPlan} (h : close g now bm p = .ok q) (i : Id) (e f : Entity)
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) :
    remainingOf bm f.val.line = remainingOf bm e.val.line ∨
      remainingOf bm f.val.line = max (remainingOf bm e.val.line) (foldedMinutes g now bm p.val i) ∨
      ∃ t, e.val.archive = some t ∧ remainingOf bm f.val.line =
        max (remainingOf bm (demoteEst bm (ownsEstimate e.val.line) (recordedEst bm t.line) e).val.line)
          (foldedMinutes g now bm p.val i) := by
  rcases close_rewrites_a_line_only_by_stamping_merging_or_folding_it h i e f hp hq with
    hl | ⟨ss, hl⟩ | ⟨ss, t, ha, hl⟩
  · exact Or.inl (by rw [hl])
  · exact Or.inr (Or.inl (by rw [hl, Field.remainingOf_setDemoted, remainingOf_foldEst]))
  · refine Or.inr (Or.inr ⟨t, ha, ?_⟩)
    rw [hl, Field.remainingOf_setDemoted, remainingOf_foldEst, carryEst_reads_as_demoteEst]

/-- **The old estimate law, where it still holds as stated**: a line whose item has
no standing record and into which nothing is folded keeps its remaining estimate at
every block length.  (Restates
`close_keeps_the_remaining_estimate_of_a_line_with_no_record`, false of a record the
fold lifted.) -/
theorem close_keeps_the_remaining_estimate_of_a_line_with_no_record_and_nothing_folded {g : Grain}
    {now : Day} {bm : Nat} {p q : WfPlan} (h : close g now bm p = .ok q) (i : Id) (e f : Entity)
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f)
    (hrec : e.val.archive = none) (hfold : foldedMinutes g now bm p.val i = 0) (bm' : Nat) :
    remainingOf bm' f.val.line = remainingOf bm' e.val.line := by
  rcases close_rewrites_a_line_with_no_record_and_nothing_folded_only_by_stamping_it h i e f hp hq hrec hfold
    with h1 | ⟨ss, h2⟩
  · rw [h1]
  · rw [h2, Field.remainingOf_setDemoted]

/-- **Narrowed F4** (`close_never_demotes_a_wall`, whose `f.val = e.val` forbids
the carry — and the rank shift a landing inside a section performs; refuted as
`close_does_not_leave_every_wall_as_it_was`, Boundary.lean).  A
recurring line or a wall keeps its box, its bytes and its tombstone through
every close; the one thing that may change is the file its record is in. -/
theorem close_never_demotes_a_wall_but_may_carry_it {g : Grain} {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close g now bm p = .ok q) (i : Id) (e f : Entity)
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f)
    (hw : e.val.recur ≠ Recur.none ∨ ∃ a b : DT, e.val.shape = Shape.interval a b) :
    f.val.skel = { e.val.skel with doc := f.val.live.doc } := by
  have hsk := close_skel h hp hq
  have hx : e.val.skel.recurring = true ∨ ∃ b, e.val.skel.wallAhead now = some b := by
    rcases hw with hw | ⟨a, b, hs⟩
    · left
      show decide (Field.viewRecur e.val.line ≠ Recur.none) = true
      exact decide_eq_true hw
    · right
      refine ⟨decide (now ≤ b.day), ?_⟩
      show (match Field.viewShape e.val.line with
            | .interval _ b => some (decide (now ≤ b.day))
            | _ => none) = _
      have : Field.viewShape e.val.line = Shape.interval a b := hs
      rw [this]
  have := stepSkel_of_exempt (x := foldFxOf g now bm p.val i)
    (closeAct_never_files_an_exempt_line (g := g) (p := p.val) hx)
  rw [hsk]
  conv => lhs; rw [this]
  rw [← hsk]
  rfl

/-- **D1, as a theorem, for every line the close does not drop** (restates
`close_files_a_taken_line_into_closeTo`, false of a child the week row drops with its
parent, which stays in its file: `close_week_drops_a_child_with_its_parent`).  A line
a close takes and does not drop is filed into `closeTo g now` — the file of the next
coarser grain containing *now* — and its skeleton is the table's row applied to it,
the child fold's estimate included.  Never `targetContaining`: see the next theorem. -/
theorem close_files_a_taken_line_it_does_not_drop_into_closeTo {g : Grain} {now : Day} {bm : Nat}
    {p q : WfPlan} (h : close g now bm p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) {r : Region}
    (hact : closeAct g now p.val e.val.skel = .file r) (hnd : dropsInto g now p.val i = none) :
    docRegion q.val f.val.live.doc = some (closeTo g now) ∧
      docKindAt q.val f.val.live.doc = kindOfGrain (coarsen g) ∧
      f.val.skel = skelAfter g r f.val.live.doc (foldFxOf g now bm p.val i) e.val.skel := by
  obtain ⟨hfr, hall⟩ := close_spec h
  have hsk := close_skel h hp hq
  have hst := (hall i).2 f hq
  rw [closeAct_frame hfr] at hst
  have hx : (foldFxOf g now bm p.val i).isDrop = false := by rw [foldFxOf_isDrop, hnd]; rfl
  cases hk : closeTarget g now p.val with
  | none =>
    have hstep : stepSkel g now p.val (foldFxOf g now bm p.val i) e.val.skel = e.val.skel := by
      rw [stepSkel_of_file hact hx, hk]
    rw [hsk, hstep, hact] at hst
    exact absurd hst (by simp)
  | some k =>
    have hstep : stepSkel g now p.val (foldFxOf g now bm p.val i) e.val.skel =
        skelAfter g r k (foldFxOf g now bm p.val i) e.val.skel := by
      rw [stepSkel_of_file hact hx, hk]
    rw [hstep] at hsk
    rcases skelAfter_doc g r k (foldFxOf g now bm p.val i) e.val.skel with hd | hd
    · have hdoc : f.val.live.doc = k := by
        have := congrArg Skel.doc hsk
        rw [hd] at this
        exact this
      obtain ⟨_, hkind, hreg⟩ := findDocIx_spec hk
      refine ⟨by rw [hfr.2.2, hdoc]; exact hreg, by rw [hfr.2.1, hdoc]; exact hkind, ?_⟩
      rw [hdoc]; exact hsk
    · rw [hsk, hd, hact] at hst
      exact absurd hst (by simp)

/-- **§6.3's week row: "Unfinished children are dropped from the week file"** — on
the kernel's side of "demotion, not deletion".  A line the week close drops keeps
its file, its tombstone and its bytes and becomes `[~]`; the line its minutes go to
is one the same close files from the same file and does not drop, and those minutes
— its own `est:` or leading estimate — are counted in that line's `foldedMinutes`
(fork-point `close_week` removed the line, `remove_line_in`; README "Stage 4 final,
step 4" records the difference). -/
theorem close_week_drops_a_child_with_its_parent {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close week now bm p = .ok q) {j r : Id} {e f : Entity}
    (hp : p.val.store.get j = some e) (hq : q.val.store.get j = some f)
    (hd : dropsInto week now p.val j = some r) :
    f.val.skel = { e.val.skel with status := .settled .dropped } ∧
      ∃ er fr, p.val.store.get r = some er ∧ q.val.store.get r = some fr ∧
        (∃ r0, closeAct week now p.val er.val.skel = .file r0) ∧ er.val.live.doc = e.val.live.doc ∧
        dropsInto week now p.val r = none ∧ remainingOf bm e.val.line ≤ foldedMinutes week now bm p.val r := by
  obtain ⟨_, _, hrn, ej, er, hj, her, hfj, hfr, hdoc⟩ := dropsInto_spec hd
  rw [hp] at hj
  injection hj with hj
  subst hj
  obtain ⟨r1, hact⟩ := filesLine_iff.1 hfj
  have hx : (foldFxOf week now bm p.val j).isDrop = true := by rw [foldFxOf_isDrop, hd]; rfl
  have hsk := close_skel h hp hq
  rw [stepSkel_of_drop hact hx] at hsk
  have hm := ((close_spec h).2 r).1
  rw [her] at hm
  have hfr' : ∃ fr, q.val.store.get r = some fr := by
    cases hq' : q.val.store.get r with
    | none => rw [hq'] at hm; simp at hm
    | some fr => exact ⟨fr, rfl⟩
  obtain ⟨fr, hfr'⟩ := hfr'
  have hown := ownMinutes_le_foldedMinutes bm hd
  unfold ownMinutes at hown
  rw [hp] at hown
  exact ⟨hsk, er, fr, her, hfr', filesLine_iff.1 hfr, hdoc, hrn, hown⟩

/-- The week row's filing, unfolded: a `[-]` record carrying the week stamp over
`refiledLineX`'s bytes, its tombstone the line as it stood. -/
theorem skelAfter_week (r : Region) (k : DocIx) (x : FoldFx) (s : Skel) :
    skelAfter week r k x s =
      ⟨k, some s.doc, some s.line, .demoted, refiledLineX x (.week (Cal.isoOf (7 * r.ix)).week) s.archLine s.line⟩ :=
  rfl

theorem demoteEst_reads_zero (bm : Nat) (u : Bool) (e : Entity) :
    remainingOf bm (demoteEst bm u 0 e).val.line = remainingOf bm e.val.line := by
  cases u with
  | true => rfl
  | false =>
    show remainingOf bm (setEst (max (remainingOf bm e.val.line) 0) e.val.line) = _
    unfold remainingOf
    rw [view_set_is_not_silent]
    simp [remainingOf]

/-- The line a week copy files forward, before the fold: the live line, or with a
standing record the record's estimate carried onto it (`carryEst`). -/
def carriedLine (e : Entity) : RawItem :=
  match e.val.archive with
  | none   => e.val.line
  | some t => carryEst t.line e.val.line

/-- Its reading is `demoteEst`'s, with the standing record's measurement (`0` when
there is none) and L15's user exception. -/
theorem remainingOf_carriedLine (bm : Nat) (e : Entity) :
    remainingOf bm (carriedLine e) =
      remainingOf bm (demoteEst bm (ownsEstimate e.val.line)
        ((e.val.archive.map (fun t => recordedEst bm t.line)).getD 0) e).val.line := by
  unfold carriedLine
  cases ha : e.val.archive with
  | none => simp only [Option.map_none, Option.getD_none]; rw [demoteEst_reads_zero]
  | some t => simp only [Option.map_some, Option.getD_some]; exact carryEst_reads_as_demoteEst bm t.line e

/-- **§6.4's `max`, on the week row's record — the law goal B3 was stated against
(and refuted: `close_week_does_not_add_a_dropped_child_to_its_parent`, Boundary.lean).**
A line the week close files forward and does not drop becomes a `[-]` record whose
remaining, at the block length the close was run with, is the larger of what the
line carried before the fold — its own reading, or L15's merge with its standing
record — and the sum of the own remaining of the children dropped with it
(fork-point `horizon::demote_est`'s `folded`: "so a week close never removes work
from the tree").  A `6b` milestone with a dropped `1b` subtask carries `6b`; a `2b`
milestone whose dropped subtasks add up to `3b` carries `3b`. -/
theorem close_week_folds_dropped_children_by_max {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close week now bm p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) {r : Region}
    (hact : closeAct week now p.val e.val.skel = .file r) (hnd : dropsInto week now p.val i = none) :
    f.val.status = .demoted ∧
      remainingOf bm f.val.line =
        max (remainingOf bm (demoteEst bm (ownsEstimate e.val.line)
              ((e.val.archive.map (fun t => recordedEst bm t.line)).getD 0) e).val.line)
          (foldedMinutes week now bm p.val i) := by
  obtain ⟨_, _, hsk⟩ := close_files_a_taken_line_it_does_not_drop_into_closeTo h hp hq hact hnd
  rw [skelAfter_week] at hsk
  have hline : f.val.line = refiledLineX (foldFxOf week now bm p.val i)
      (.week (Cal.isoOf (7 * r.ix)).week) (e.val.archive.map Tomb.line) e.val.line :=
    congrArg Skel.line hsk
  refine ⟨congrArg Skel.status hsk, ?_⟩
  rw [hline, ← remainingOf_carriedLine, ← remainingOf_foldEst, ← foldFxOf_apply week now bm p.val i]
  unfold carriedLine
  cases ha : e.val.archive with
  | none => simp only [Option.map_none, refiledLineX]; rw [Field.remainingOf_setDemoted]
  | some t => simp only [Option.map_some, refiledLineX]; rw [Field.remainingOf_setDemoted]

/-- **One direction: a stale parent is lifted.**  When the children dropped with a
line add up to more than it carried, its record carries their sum. -/
theorem close_week_lifts_a_parent_its_dropped_children_outweigh {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close week now bm p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) {r : Region}
    (hact : closeAct week now p.val e.val.skel = .file r) (hnd : dropsInto week now p.val i = none)
    (hlt : remainingOf bm (carriedLine e) < foldedMinutes week now bm p.val i) :
    remainingOf bm f.val.line = foldedMinutes week now bm p.val i ∧
      remainingOf bm e.val.line < remainingOf bm f.val.line ∨
      (e.val.archive.isSome ∧ remainingOf bm f.val.line = foldedMinutes week now bm p.val i) := by
  have hm := (close_week_folds_dropped_children_by_max h hp hq hact hnd).2
  rw [← remainingOf_carriedLine, Nat.max_eq_right (Nat.le_of_lt hlt)] at hm
  cases ha : e.val.archive with
  | none =>
    left
    have hc : carriedLine e = e.val.line := by unfold carriedLine; rw [ha]
    rw [hc] at hlt
    exact ⟨hm, by rw [hm]; exact hlt⟩
  | some t => exact Or.inr ⟨by simp, hm⟩

/-- **The other direction: a parent that covers its children is left alone.**  When
the line already carries at least the children's minutes, the fold writes nothing:
its record is byte for byte the one the week row files with no fold at all. -/
theorem close_week_keeps_a_parent_that_covers_its_dropped_children {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close week now bm p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) {r : Region}
    (hact : closeAct week now p.val e.val.skel = .file r) (hnd : dropsInto week now p.val i = none)
    (hle : foldedMinutes week now bm p.val i ≤ remainingOf bm (carriedLine e)) :
    f.val.skel = skelAfter week r f.val.live.doc .none e.val.skel := by
  obtain ⟨_, _, hsk⟩ := close_files_a_taken_line_it_does_not_drop_into_closeTo h hp hq hact hnd
  rw [hsk, skelAfter_week, skelAfter_week]
  have happ : (foldFxOf week now bm p.val i).apply (carriedLine e) = carriedLine e := by
    rw [foldFxOf_apply, foldEst_of_le hle]
  unfold carriedLine at happ
  have hl : refiledLineX (foldFxOf week now bm p.val i) (.week (Cal.isoOf (7 * r.ix)).week)
      e.val.skel.archLine e.val.skel.line =
      refiledLineX .none (.week (Cal.isoOf (7 * r.ix)).week) e.val.skel.archLine e.val.skel.line := by
    show refiledLineX _ _ (e.val.archive.map Tomb.line) e.val.line = refiledLineX _ _ (e.val.archive.map Tomb.line) e.val.line
    cases ha : e.val.archive with
    | none =>
      simp only [ha] at happ
      simp only [Option.map_none, refiledLineX, happ]
      rfl
    | some t =>
      simp only [ha] at happ
      simp only [Option.map_some, refiledLineX, happ]
      rfl
  rw [hl]

/-- **What B3 meant, and holds: a close never removes a dropped child's work.**  The
child's own remaining is at most the remaining of the record its minutes went to —
not added to the parent's (that is `close_week_does_not_add_a_dropped_child_to_its_parent`,
refuted), but covered by it, by §6.4's `max`. -/
theorem close_week_keeps_a_dropped_childs_remaining_in_its_parents_record {now : Day} {bm : Nat}
    {p q : WfPlan} (h : close week now bm p = .ok q) {i j : Id} {ec fp : Entity}
    (hd : dropsInto week now p.val j = some i)
    (hcp : p.val.store.get j = some ec) (hiq : q.val.store.get i = some fp) :
    remainingOf bm ec.val.line ≤ remainingOf bm fp.val.line := by
  obtain ⟨_, _, hrn, ej, er, hj, her, _, hfr, _⟩ := dropsInto_spec hd
  obtain ⟨r0, hact⟩ := filesLine_iff.1 hfr
  have hm := (close_week_folds_dropped_children_by_max h her hiq hact hrn).2
  have hown := ownMinutes_le_foldedMinutes bm hd
  unfold ownMinutes at hown
  rw [hcp] at hown
  rw [hm]
  exact Nat.le_trans hown (Nat.le_max_right _ _)

/-- **D1 separates from the rule it replaced.**  A day close files into the
week containing *now*; whenever the closed day's week is not now's week — a
close run late — that is not the week the closed day belonged to
(`targetContaining`, fork-point `horizon::close_day`). -/
theorem close_day_files_into_the_week_of_now {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close day now bm p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) {r : Region}
    (hact : closeAct day now p.val e.val.skel = .file r)
    (hlate : Cal.weekOrdinal r.ix ≠ Cal.weekOrdinal now) :
    docRegion q.val f.val.live.doc = some (closeTo day now) ∧
      docRegion q.val f.val.live.doc ≠ some (targetContaining day r.ix) := by
  have ⟨hreg, _, _⟩ := close_files_a_taken_line_it_does_not_drop_into_closeTo h hp hq hact
    (dropsInto_of_asAnyLine rfl)
  refine ⟨hreg, ?_⟩
  rw [hreg]
  intro hc
  injection hc with hc
  exact (impl_rule_disagrees_iff day r.ix now).2 hlate hc.symm

/-- **F4's carry.**  A wall still ahead, in a closed region a close takes it
from, lands in the live week — the one week file the planner reads (§6.2) —
with its box, bytes and tombstone untouched. -/
theorem close_carries_a_wall_that_is_still_ahead {g : Grain} {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close g now bm p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) {r : Region}
    (hreg : closedRegionOf g now p.val e.val.live.doc = some r)
    (htakes : (closePolicy g).takes e.val.status = true)
    (hrec : e.val.recur = Recur.none) {a b : DT} (hs : e.val.shape = Shape.interval a b)
    (hahead : now ≤ b.day) :
    docRegion q.val f.val.live.doc = some (regionOf week now) ∧
      docKindAt q.val f.val.live.doc = .week ∧
      f.val.skel = { e.val.skel with doc := f.val.live.doc } := by
  obtain ⟨hfr, hall⟩ := close_spec h
  have hsk := close_skel h hp hq
  have hst := (hall i).2 f hq
  rw [closeAct_frame hfr] at hst
  have hact : closeAct g now p.val e.val.skel = .carry := by
    unfold closeAct
    show (match closedRegionOf g now p.val e.val.live.doc with
          | none => CloseAct.stay
          | some r => _) = _
    rw [hreg]
    have hrec' : e.val.skel.recurring = false := by
      show decide (Field.viewRecur e.val.line ≠ Recur.none) = false
      have : Field.viewRecur e.val.line = Recur.none := hrec
      simp [this]
    have hw : e.val.skel.wallAhead now = some true := by
      show (match Field.viewShape e.val.line with
            | .interval _ b => some (decide (now ≤ b.day))
            | _ => none) = _
      have : Field.viewShape e.val.line = Shape.interval a b := hs
      rw [this]
      simp [hahead]
    have htakes' : (closePolicy g).takes e.val.skel.status = true := htakes
    have hov : e.val.skel.overdue now = false := Skel.overdue_of_wallAhead hw
    simp [htakes', hrec', hw, hov, (closePolicy_exemptions g).2, exemptAct]
  cases hk : carryTarget now p.val with
  | none =>
    have hstep : stepSkel g now p.val (foldFxOf g now bm p.val i) e.val.skel = e.val.skel := by
      unfold stepSkel; simp only [hact, hk]
    rw [hsk, hstep, hact] at hst
    exact absurd hst (by simp)
  | some k =>
    have hstep : stepSkel g now p.val (foldFxOf g now bm p.val i) e.val.skel = { e.val.skel with doc := k } := by
      unfold stepSkel; simp only [hact, hk]
    rw [hstep] at hsk
    have hdoc : f.val.live.doc = k := congrArg Skel.doc hsk
    obtain ⟨_, hkind, hreg'⟩ := findDocIx_spec hk
    refine ⟨by rw [hfr.2.2, hdoc]; exact hreg', by rw [hfr.2.1, hdoc]; exact hkind, ?_⟩
    rw [hsk, hdoc]

/-! ## The check bites: every refusal is named, none is a skip -/

/-- A line to file and no document to file it into is `noTarget`. -/
theorem closeOne_refuses_a_missing_target {g : Grain} {now : Day} {x : FoldFx} {i : Id} {p : WfPlan}
    {e : Entity} {r : Region} (hget : p.val.store.get i = some e)
    (hact : closeAct g now p.val e.val.skel = .file r) (hx : x.isDrop = false)
    (hnone : closeTarget g now p.val = none) : closeOne g now x i p = .error .noTarget := by
  unfold closeOne
  simp only [hget, hact, hx, hnone, Bool.false_eq_true, ↓reduceIte]

/-- A wall to carry and no live week to carry it into is `noTarget` too — the
close does not leave it stranded in the archive and call that success. -/
theorem closeOne_refuses_a_carry_with_no_live_week {g : Grain} {now : Day} {i : Id}
    {x : FoldFx} {p : WfPlan} {e : Entity} (hget : p.val.store.get i = some e)
    (hact : closeAct g now p.val e.val.skel = .carry)
    (hnone : carryTarget now p.val = none) : closeOne g now x i p = .error .noTarget := by
  unfold closeOne
  simp only [hget, hact, hnone]

/-- A destination with no section to receive the line is `noSection`. -/
theorem closeOne_refuses_a_missing_section {g : Grain} {now : Day} {x : FoldFx} {i : Id} {p : WfPlan}
    {e : Entity} {r : Region} {k : DocIx} (hget : p.val.store.get i = some e)
    (hact : closeAct g now p.val e.val.skel = .file r) (hx : x.isDrop = false)
    (hk : closeTarget g now p.val = some k)
    (hsec : landingSpot p.val k (closePolicy g).landing (sectionAt p.val e.val.live) =
      .error .noSection) : closeOne g now x i p = .error .noSection := by
  unfold closeOne
  simp only [hget, hact, hx, hk, hsec, Bool.false_eq_true, ↓reduceIte]

/-- **The post-state check bites.**  A filed line whose post-state fails
`planWf` — a dated item filed into a month file that holds outcomes only, a
tombstone the loader could not orient — is refused as `badHorizon`, and nothing
is written. -/
theorem closeOne_refuses_an_ill_formed_post_state {g : Grain} {now : Day} {x : FoldFx} {i : Id}
    {p : WfPlan} {e f : Entity} {r : Region} {k : DocIx}
    (hget : p.val.store.get i = some e)
    (hact : closeAct g now p.val e.val.skel = .file r) (hx : x.isDrop = false)
    (hk : closeTarget g now p.val = some k)
    (hspot : landingSpot p.val k (closePolicy g).landing (sectionAt p.val e.val.live) = .ok none)
    (hf : fileE g r x ⟨k, endRank p.val k⟩ e = .ok f)
    (hbad : ¬ planWf { p.val with store := p.val.store.set i f (by rw [hget]; rfl) } = true) :
    closeOne g now x i p = .error .badHorizon := by
  unfold closeOne
  simp only [hget, hact, hx, hk, hspot, Bool.false_eq_true, ↓reduceIte]
  apply guardStray_of_error
  unfold landAt
  simp only
  unfold WfPlan.mapAt
  split
  · rename_i hn; rw [hget] at hn; simp at hn
  · rename_i a hget'
    rw [hget] at hget'
    injection hget' with hget'
    subst hget'
    rw [hf]
    simp only [dif_neg hbad]

/-! ### Gap 53: a standing record is merged, and the close no longer refuses it

§4.3's own pre-close pair — a `[ ]` line in a week beside its `[-]` copy under a
month's `# Demoted` — made the week close answer `alreadyDemoted` until the copy
became `refile` (README gap 53, stage-4 hardening step 2).  The two directions:
a close answers `alreadyDemoted` only at the week row, over an item whose tombstone
is not its `# Demoted` record (`closeOne_refuses_alreadyDemoted_only_over_a_stray_tomb`,
`closeOne_never_merges_into_a_stray_tomb` — the repair of step 2's
`close_never_refuses_alreadyDemoted`, which let the merge delete a `[-]` line from a
closed week), and what a week close writes for a line with a record is fork-point
`demote_one`'s merge with L15's floor (`close_week_merges_a_standing_record_it_does_not_drop`); the
loaded-plan witnesses are in `Boundary.lean` (`the_week_close_merges_each_standing_record`,
`a_stray_tomb_refuses_the_week_close`). -/

theorem mapAt_error {p : WfPlan} {i : Id} {F : Entity → Except KErr Entity} {x : KErr}
    (h : p.mapAt i F = .error x) :
    x = .noSuchId ∨ x = .badHorizon ∨ ∃ e, p.val.store.get i = some e ∧ F e = .error x := by
  unfold WfPlan.mapAt at h
  split at h
  · injection h with h; exact Or.inl h.symm
  · rename_i e hget
    split at h
    · rename_i k hk
      injection h with h; subst h
      exact Or.inr (Or.inr ⟨e, hget, hk⟩)
    · split at h
      · simp at h
      · injection h with h; exact Or.inr (Or.inl h.symm)

/-- `landAt` refuses as `shiftAt` and `mapAt` do, or with the transform's own
refusal of the entity at `i` — ranks shifted, box unchanged. -/
theorem landAt_error {p : WfPlan} {k : DocIx} {spot : Option Nat} {i : Id}
    {f : Site → Entity → Except KErr Entity} {x : KErr} (h : landAt p k spot i f = .error x) :
    x = .noSuchId ∨ x = .badHorizon ∨ ∃ t e e0, p.val.store.get i = some e0 ∧
      e.val.status = e0.val.status ∧ f t e = .error x := by
  cases spot with
  | none =>
    rcases mapAt_error h with h1 | h1 | ⟨e, he, hf⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨_, e, e, he, rfl, hf⟩)
  | some n =>
    unfold landAt at h
    simp only at h
    cases h1 : p.shiftAt k n with
    | error y =>
      rw [h1] at h
      injection h with h
      unfold WfPlan.shiftAt at h1
      split at h1
      · simp at h1
      · injection h1 with h1; exact Or.inr (Or.inl (h.symm.trans h1.symm))
    | ok q =>
      rw [h1] at h
      rcases mapAt_error h with h2 | h2 | ⟨e, he, hf⟩
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
      · have hv := WfPlan.shiftAt_val h1
        have hg : q.val.store.get i = (p.val.store.get i).map (Entity.shiftIn k n) := by rw [hv]; rfl
        rw [hg] at he
        cases hp : p.val.store.get i with
        | none => rw [hp] at he; simp at he
        | some e0 =>
          rw [hp] at he
          simp only [Option.map_some, Option.some.injEq] at he
          subst he
          exact Or.inr (Or.inr ⟨_, Entity.shiftIn k n e0, e0, rfl, rfl, hf⟩)

theorem landingSpot_error {p : PlanCore} {k : DocIx} {l : Landing} {src : Option (List Char)}
    {x : KErr} (h : landingSpot p k l src = .error x) : x = .noTarget ∨ x = .noSection := by
  unfold landingSpot at h
  split at h
  · injection h with h; exact Or.inl h.symm
  · split at h
    · simp at h
    · split at h
      · injection h with h; exact Or.inr h.symm
      · simp at h
    · split at h
      · simp at h
      · split at h
        · injection h with h; exact Or.inr h.symm
        · simp at h
    · split at h
      · injection h with h; exact Or.inr h.symm
      · simp at h

/-- The only filing transform that can answer `alreadyDemoted` is the week row's
`refile`, and only for a line whose own box is `[-]`. -/
theorem fileE_alreadyDemoted {g : Grain} {r : Region} {x : FoldFx} {t : Site} {e : Entity}
    (h : fileE g r x t e = .error .alreadyDemoted) :
    (closePolicy g).disposition = .copy ∧ e.val.status = .demoted := by
  unfold fileE at h
  cases hd : (closePolicy g).disposition with
  | move =>
    simp only [hd, moveTo, lift] at h
    split at h <;> simp at h
  | moveReopening =>
    simp only [hd, lift] at h
    split at h <;> simp at h
  | copy =>
    simp only [hd] at h
    cases hs : closeStamp g r.ix with
    | none => simp [hs] at h
    | some st =>
      simp only [hs] at h
      exact ⟨rfl, refileX_refuses_only_a_record h⟩

/-- **Which step answers `alreadyDemoted`** (restates
`closeOne_never_refuses_alreadyDemoted`, false since the stage-4 hardening repair:
a week close over a stray tombstone refuses).  Only a copying row, and only over
an item whose tombstone is not its `# Demoted` record. -/
theorem closeOne_refuses_alreadyDemoted_only_over_a_stray_tomb {g : Grain} {now : Day}
    {x : FoldFx} {i : Id} {p : WfPlan} (h : closeOne g now x i p = .error .alreadyDemoted) :
    (closePolicy g).disposition = .copy ∧ ∃ e t, p.val.store.get i = some e ∧
      e.val.archive = some t ∧ demotedRecordPlacement p.val t.site = false := by
  unfold closeOne at h
  split at h
  · simp at h
  · rename_i e hget
    split at h
    · simp at h
    · split at h
      · simp at h
      · rcases landAt_error h with h1 | h1 | ⟨t, e', _, _, _, hf⟩
        · simp at h1
        · simp at h1
        · simp only [moveTo, lift] at hf
          split at hf <;> simp at hf
    · rename_i r hact
      split at h
      · rcases mapAt_error h with h1 | h1 | ⟨_, _, hf⟩
        · simp at h1
        · simp at h1
        · simp [dropE] at hf
      · split at h
        · simp at h
        · split at h
          · rename_i y hy
            injection h with h; subst h
            rcases landingSpot_error hy with h1 | h1 <;> simp at h1
          · rcases guardStray_error h with hl | ⟨_, hb, _⟩
            · rcases landAt_error hl with h1 | h1 | ⟨t, e', e0, he0, hst, hf⟩
              · simp at h1
              · simp at h1
              · rw [hget] at he0
                injection he0 with he0
                subst he0
                obtain ⟨hcopy, hdem⟩ := fileE_alreadyDemoted hf
                have htakes : (closePolicy g).takes e'.val.status = true := by
                  rw [hst]
                  unfold closeAct at hact
                  split at hact
                  · simp at hact
                  · split at hact
                    · simp at hact
                    · rename_i hn
                      exact Bool.not_eq_false _ |>.mp hn
                rw [hdem, closePolicy_takes_the_demoted_record_only_at_month] at htakes
                exact absurd (by simpa using htakes) (closePolicy_copies_only_below_month g hcopy)
            · unfold copiesOverAStrayTomb hasAStrayTomb at hb
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
              obtain ⟨hcopy, hs⟩ := hb
              cases ha : e.val.archive with
              | none => simp [ha] at hs
              | some t =>
                simp only [ha, Bool.not_eq_true'] at hs
                exact ⟨hcopy, e, t, hget, ha, hs⟩
    · split at h
      · simp at h
      · split at h
        · rename_i y hy
          injection h with h; subst h
          rcases landingSpot_error hy with h1 | h1 <;> simp at h1
        · rcases landAt_error h with h1 | h1 | ⟨t, e', _, _, _, hf⟩
          · simp at h1
          · simp at h1
          · simp only [moveTo, lift] at hf
            split at hf <;> simp at hf

/-- **The old law, where it still holds as stated**: a step over an item with no
stray tombstone never answers `alreadyDemoted`. -/
theorem closeOne_never_refuses_alreadyDemoted_without_a_stray_tomb (g : Grain) (now : Day)
    (x : FoldFx) (i : Id) (p : WfPlan) (hs : ∀ e, p.val.store.get i = some e → hasAStrayTomb p.val e = false) :
    closeOne g now x i p ≠ .error .alreadyDemoted := by
  intro h
  obtain ⟨_, e, t, hget, ha, hr⟩ := closeOne_refuses_alreadyDemoted_only_over_a_stray_tomb h
  have := hs e hget
  simp [hasAStrayTomb, ha, hr] at this

/-- **The repair's positive direction.**  A week-row step that takes a line whose
item's tombstone is not its `# Demoted` record never succeeds: whatever its landing
does, the record is not merged and the tombstone is not deleted. -/
theorem closeOne_never_merges_into_a_stray_tomb {g : Grain} {now : Day} {x : FoldFx} {i : Id}
    {p q : WfPlan} {e : Entity} {t : Tomb} (hget : p.val.store.get i = some e)
    (hcopy : (closePolicy g).disposition = .copy) (harch : e.val.archive = some t)
    (hrec : demotedRecordPlacement p.val t.site = false) {r : Region}
    (hact : closeAct g now p.val e.val.skel = .file r) (hx : x.isDrop = false) :
    closeOne g now x i p ≠ .ok q := by
  intro h
  unfold closeOne at h
  simp only [hget, hact, hx, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · have hb := (guardStray_ok h).2
      simp [copiesOverAStrayTomb, hasAStrayTomb, hcopy, harch, hrec] at hb

/-- **Which close answers `alreadyDemoted`** (restates
`close_never_refuses_alreadyDemoted`, refuted on a loaded plan by
`a_stray_tomb_refuses_the_week_close`): only a copying row — §6.3's week row —
and only at a step over a stray tombstone. -/
theorem close_answers_alreadyDemoted_only_at_a_copying_row {g : Grain} {now : Day} {bm : Nat} {p : WfPlan}
    (h : close g now bm p = .error .alreadyDemoted) : (closePolicy g).disposition = .copy := by
  revert h
  show (closeCands g now p.val).foldlM (fun q i => closeOne g now (foldFxOf g now bm p.val i) i q) p = _ → _
  generalize foldFxOf g now bm p.val = fx
  generalize closeCands g now p.val = l
  induction l generalizing p with
  | nil => intro h; cases h
  | cons i rest ih =>
    simp only [List.foldlM_cons]
    cases h1 : closeOne g now (fx i) i p with
    | error x =>
      intro h
      injection h with h
      subst h
      exact (closeOne_refuses_alreadyDemoted_only_over_a_stray_tomb h1).1
    | ok q => exact ih

/-- **§4.3's pre-close pair closes, merged (README gap 53)** — for a line the week row
does not drop (restates `close_week_merges_a_standing_record`, false of a child dropped
with its parent, which keeps its record and becomes `[~]`, and of a record the child
fold lifted, whose line is not the live line with only the stamps set:
`a_dropped_child_keeps_its_record_unmerged`, Boundary.lean).  A week close that files
forward a line whose item already has a `# Demoted` record rewrites that record: the
line it leaves is the tombstone, the record's box is `[-]`, its stamps are
fork-point `merge_stamps` — the record's history, then the line's, then the closed
week's, each once (`mergeStamps_spec`, `mergeStamps_of_nodup`) — and its estimate is
L15's, under B3's fold: when the line owns an estimate it stands, with only the
stamps set and the children's floor applied (`demoteEst_respects_user`, `foldEst`);
when it owns none, the record's measured remaining is a floor, and so is the line's
own reading (`demoteEst_conserves`); and the minutes of the children dropped with it
are a floor either way (`foldEst`). -/
theorem close_week_merges_a_standing_record_it_does_not_drop {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close week now bm p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) {r : Region}
    (hact : closeAct week now p.val e.val.skel = .file r) (hnd : dropsInto week now p.val i = none)
    {t : Tomb} (harch : e.val.archive = some t) :
    f.val.archive.map Tomb.line = some e.val.line ∧ f.val.status = .demoted ∧
      f.val.stamps = mergeStamps (stampsOfLine t.line) e.val.stamps
        (.week (Cal.isoOf (7 * r.ix)).week) ∧
      (ownsEstimate e.val.line = true →
        f.val.line = Field.setDemoted f.val.stamps (foldEst bm (foldedMinutes week now bm p.val i) e.val.line)) ∧
      (ownsEstimate e.val.line = false →
        recordedEst bm t.line ≤ remainingOf bm f.val.line ∧
          remainingOf bm e.val.line ≤ remainingOf bm f.val.line) ∧
      foldedMinutes week now bm p.val i ≤ remainingOf bm f.val.line := by
  obtain ⟨_, _, hsk⟩ := close_files_a_taken_line_it_does_not_drop_into_closeTo h hp hq hact hnd
  rw [skelAfter_week] at hsk
  have harchL : e.val.skel.archLine = some t.line := by simp [Core.skel, harch]
  have hline : f.val.line = Field.setDemoted
      (mergeStamps (stampsOfLine t.line) e.val.stamps (.week (Cal.isoOf (7 * r.ix)).week))
      (foldEst bm (foldedMinutes week now bm p.val i) (carryEst t.line e.val.line)) := by
    have := congrArg Skel.line hsk
    rw [harchL] at this
    exact this.trans (by simp only [refiledLineX, foldFxOf_apply]; rfl)
  have hst : f.val.stamps = mergeStamps (stampsOfLine t.line) e.val.stamps
      (.week (Cal.isoOf (7 * r.ix)).week) := by
    show (Field.viewDemoted f.val.line).getD [] = _
    rw [hline, Field.view_set_demoted _ _
      (List.ne_nil_of_mem (((mergeStamps_spec _ _ _).2 _).2 (Or.inr (Or.inr rfl))))]
    rfl
  have hread : remainingOf bm f.val.line =
      max (remainingOf bm (carryEst t.line e.val.line)) (foldedMinutes week now bm p.val i) := by
    rw [hline, Field.remainingOf_setDemoted, remainingOf_foldEst]
  refine ⟨congrArg Skel.archLine hsk, congrArg Skel.status hsk, hst, fun hu => ?_, fun hu => ?_, ?_⟩
  · rw [hline, hst]
    simp [carryEst, hu]
  · have hl : remainingOf bm (carryEst t.line e.val.line) =
        remainingOf bm (demoteEst bm false (recordedEst bm t.line) e).val.line := by
      rw [carryEst_reads_as_demoteEst, hu]
    have hc := demoteEst_conserves bm (recordedEst bm t.line) e
    rw [hread, hl]
    exact ⟨Nat.le_trans hc.1 (Nat.le_max_left _ _), Nat.le_trans hc.2 (Nat.le_max_left _ _)⟩
  · rw [hread]; exact Nat.le_max_right _ _

/-- **A refusal is the close's refusal.**  The fold does not skip a step that
fails: the first candidate's refusal is the whole close's answer, and no later
step runs. -/
theorem close_refuses_what_its_first_step_refuses {g : Grain} {now : Day} {bm : Nat} {p : WfPlan}
    {i : Id} {rest : List Id} {x : KErr} (hc : closeCands g now p.val = i :: rest)
    (h1 : closeOne g now (foldFxOf g now bm p.val i) i p = .error x) : close g now bm p = .error x := by
  show (closeCands g now p.val).foldlM (fun q i => closeOne g now (foldFxOf g now bm p.val i) i q) p = _
  rw [hc, List.foldlM_cons, h1]
  rfl


/-- **The other direction: a close with nothing to take succeeds and writes
nothing.**  An empty candidate set is the identity, not a refusal. -/
theorem close_without_candidates_is_the_identity {g : Grain} {now : Day} {bm : Nat} {p : WfPlan}
    (h : closeCands g now p.val = []) : close g now bm p = .ok p := by
  show (closeCands g now p.val).foldlM (fun q i => closeOne g now (foldFxOf g now bm p.val i) i q) p = _
  rw [h]
  rfl

/-! ## L16: closing twice is closing once (stage 4 step 3)

`close_spec` already says that after a successful close no line is one the same
close would take; a candidate set is exactly the lines a close would take, so
the second run's is empty, and an empty candidate set is the identity. -/

/-- A plan in which no line is one a close of grain `g` at `now` would take has
no candidates for it. -/
theorem closeCands_eq_nil_of_stay {g : Grain} {now : Day} {p : PlanCore}
    (h : ∀ i f, p.store.get i = some f → closeAct g now p f.val.skel = .stay) :
    closeCands g now p = [] := by
  have hs : closeCandSet g now p = [] := by
    unfold closeCandSet
    rw [List.filter_eq_nil_iff]
    intro i _
    cases hg : p.store.get i with
    | none => simp
    | some e => simp [h i e hg]
  have hp := closeCands_perm g now p
  rw [hs] at hp
  exact hp.eq_nil

/-- **L16 (discharged from `Goals.lean`, as stated): `close g now` is
idempotent.**  Closing grain `g` twice at the same instant `now` is closing it
once: whatever plan a successful close returns, the same close returns it
unchanged.

**Which idempotence this is.**  It is the fold on `WfPlan` — a fact about the
plan *value*, with `g` and `now` held fixed — and nothing else.  It is **not**
§6.3's "runs automatically on the first command after the period ends
(idempotent; recorded in `state.json`)": that one is a Rust fact about the
`closed` map the host keeps across invocations and instants, and no kernel
statement is about it.  Nor is it a claim across instants: a close at a later `now`
may take lines this one left, because more regions are closed by then
(`closed_is_stable_in_time`).

**Why it holds.**  After the fold every line either stayed, was filed into
`closeTo g now`, carried into the live week or moved to the backlog, and none of
those files is a closed region (`closeTo_target_is_open`, `regionOf_is_open`,
`closeAct_of_regionless`) — or, since goal B3's repair, it is a child the week row
dropped with its parent, and a `[~]` line is settled, which no row takes
(`closeAct_of_settled`); all read through `close_leaves_no_line_it_would_take`.  So
the second run's candidate set is empty and the fold is the identity
(`close_without_candidates_is_the_identity`), whatever the child fold would ask of
it: a fold over no candidates asks nothing.
That is the target D1 chose; see the README's stage-4 step-3 block for where the
rule it replaced would and would not have broken this argument.

**The hypothesis is satisfiable** on loaded plans at all three grains:
`the_week_close_copies_carries_and_leaves_the_rest`,
`the_day_close_files_into_the_week_of_now` and
`the_month_close_moves_each_line_into_its_section` (Boundary.lean) each decide a
successful close. -/
theorem close_is_idempotent (g : Grain) (now : Day) (bm : Nat) (p q : WfPlan)
    (h : close g now bm p = .ok q) : close g now bm q = .ok q :=
  close_without_candidates_is_the_identity
    (closeCands_eq_nil_of_stay (fun i f hq => close_leaves_no_line_it_would_take h i f hq))

/-! ## L17's finding: at one instant, closes of distinct grains move every line alike

L17 ("`close week` and `close month` commute") is false as written and is refuted
on a loaded plan in `Boundary.lean` (`close_week_and_close_month_do_not_commute`).
The reason is **not** the one its goal expected — that the week close's output
becomes the month close's input in one order and not the other.  With D1's
target, no close's output is ever in a closed region at the same `now`, so
neither close sees the other's work; what differs is only *rank*, where both
land a line at the end of one section of the one open month file.  This section
proves the part that does commute: every line's rank-free skeleton. -/

theorem stepSkel_of_stay {g : Grain} {now : Day} {p : PlanCore} {x : FoldFx} {s : Skel}
    (h : closeAct g now p s = .stay) : stepSkel g now p x s = s := by
  unfold stepSkel; rw [h]

/-- The fold's argument matters only for a line the close takes. -/
theorem stepSkel_congr_fx {g : Grain} {now : Day} {p : PlanCore} {x y : FoldFx} {s : Skel}
    (h : closeAct g now p s ≠ .stay → x = y) : stepSkel g now p x s = stepSkel g now p y s := by
  by_cases hs : closeAct g now p s = .stay
  · rw [stepSkel_of_stay hs, stepSkel_of_stay hs]
  · rw [h hs]

theorem closeAct_of_closedRegionOf_none {g : Grain} {now : Day} {p : PlanCore} {s : Skel}
    (h : closedRegionOf g now p s.doc = none) : closeAct g now p s = .stay := by
  unfold closeAct; rw [h]

theorem closedRegionOf_spec {g : Grain} {now : Day} {p : PlanCore} {k : DocIx} {r : Region}
    (h : closedRegionOf g now p k = some r) :
    docRegion p k = some r ∧ docKindAt p k = kindOfGrain g ∧ r.grain = g ∧ Closed r now := by
  unfold closedRegionOf at h
  cases hr : docRegion p k with
  | none => rw [hr] at h; simp at h
  | some r0 =>
    rw [hr] at h
    simp only at h
    split at h
    · rename_i hc
      injection h with h
      subst h
      exact ⟨rfl, hc.1, hc.2.1, hc.2.2⟩
    · simp at h

/-- A file is a closed region of at most one grain: a line one close acts on is
a line every close of another grain leaves where it is. -/
theorem closeAct_of_another_grain {g g' : Grain} {now : Day} {p : PlanCore} {s : Skel}
    (hne : g ≠ g') (h : closeAct g now p s ≠ .stay) : closeAct g' now p s = .stay := by
  apply closeAct_of_closedRegionOf_none
  cases h1 : closedRegionOf g now p s.doc with
  | none => exact absurd (closeAct_of_closedRegionOf_none h1) h
  | some r =>
    cases h2 : closedRegionOf g' now p s.doc with
    | none => rfl
    | some r' =>
      obtain ⟨hr, _, hg, _⟩ := closedRegionOf_spec h1
      obtain ⟨hr', _, hg', _⟩ := closedRegionOf_spec h2
      rw [hr] at hr'
      injection hr' with hrr
      subst hrr
      exact absurd (hg.symm.trans hg') hne

/-- **Where a step puts a line it moves, no close of any grain at the same instant
takes it from.**  Either the step left the skeleton alone, or the file it now names is
`closeTo g now`, the live week or the backlog, and none of them is closed — the D1
fact L16 and this section both run on, stated once for every pair of grains.  (Its
statement gained the fold's argument and the hypothesis that the fold does not drop
the line at B3's repair: a dropped child stays in its closed file, settled — the
general form is `stepSkel_leaves_nothing_a_close_takes`.) -/
theorem stepSkel_lands_outside_every_closed_region (g g' : Grain) (now : Day) (p : PlanCore)
    (x : FoldFx) (s : Skel) (hx : x.isDrop = false) :
    stepSkel g now p x s = s ∨ closedRegionOf g' now p (stepSkel g now p x s).doc = none := by
  have hopen : ∀ k r, docRegion p k = some r → ¬ Closed r now →
      closedRegionOf g' now p k = none := by
    intro k r hr ho
    unfold closedRegionOf
    rw [hr]
    simp [ho]
  cases hact : closeAct g now p s with
  | stay => exact Or.inl (stepSkel_of_stay hact)
  | carry =>
    unfold stepSkel
    rw [hact]
    cases hk : carryTarget now p with
    | none => exact Or.inl rfl
    | some k =>
      obtain ⟨_, _, hreg⟩ := findDocIx_spec hk
      exact Or.inr (hopen k _ hreg (regionOf_is_open week now))
  | file r =>
    rw [stepSkel_of_file hact hx]
    cases hk : closeTarget g now p with
    | none => exact Or.inl rfl
    | some k =>
      obtain ⟨_, _, hreg⟩ := findDocIx_spec hk
      rcases skelAfter_doc g r k x s with hd | hd
      · right; simp only; rw [hd]; exact hopen k _ hreg (closeTo_target_is_open g now)
      · exact Or.inl hd
  | overdue =>
    unfold stepSkel
    rw [hact]
    cases hk : overdueTarget p with
    | none => exact Or.inl rfl
    | some k =>
      obtain ⟨_, _, hreg⟩ := overdueTarget_spec hk
      right
      unfold closedRegionOf
      simp only
      rw [hreg]

/-- **Whatever a step does to a line, no close at the same instant takes it again** —
it moved the line out of every closed region, or it dropped it, and a `[~]` line is
settled; or it left the line alone.  The L19 theorems and L17's commuting half run
on this. -/
theorem stepSkel_leaves_nothing_a_close_takes (g g' : Grain) (now : Day) (p : PlanCore)
    (x : FoldFx) (s : Skel) :
    stepSkel g now p x s = s ∨ closeAct g' now p (stepSkel g now p x s) = .stay := by
  cases hx : x.isDrop with
  | false =>
    rcases stepSkel_lands_outside_every_closed_region g g' now p x s hx with h | h
    · exact Or.inl h
    · exact Or.inr (closeAct_of_closedRegionOf_none h)
  | true =>
    cases hact : closeAct g now p s with
    | file r =>
      rw [stepSkel_of_drop hact hx]
      exact Or.inr (closeAct_of_settled _ _ _ _ _)
    | stay => exact Or.inl (stepSkel_of_stay hact)
    | carry =>
      unfold stepSkel; rw [hact]
      cases hk : carryTarget now p with
      | none => exact Or.inl rfl
      | some k =>
        obtain ⟨_, _, hreg⟩ := findDocIx_spec hk
        right
        apply closeAct_of_closedRegionOf_none
        unfold closedRegionOf
        simp only
        rw [hreg]
        simp [regionOf_is_open week now]
    | overdue =>
      unfold stepSkel; rw [hact]
      cases hk : overdueTarget p with
      | none => exact Or.inl rfl
      | some k =>
        obtain ⟨_, _, hreg⟩ := overdueTarget_spec hk
        right
        exact closeAct_of_regionless hreg

/-- One line's skeleton, closed at two grains against one plan's files, comes
out the same in either order (at one grain the two sides are one expression).  The
fold's argument is a choice per grain (`xs`), as a close computes one per grain. -/
theorem stepSkel_comm (g g' : Grain) (now : Day) (p : PlanCore) (xs : Grain → FoldFx) (s : Skel) :
    stepSkel g' now p (xs g') (stepSkel g now p (xs g) s) =
      stepSkel g now p (xs g) (stepSkel g' now p (xs g') s) := by
  by_cases hne : g = g'
  · rw [hne]
  by_cases hg : closeAct g now p s = .stay
  · rw [stepSkel_of_stay hg]
    rcases stepSkel_leaves_nothing_a_close_takes g' g now p (xs g') s with ht | ht
    · rw [ht, stepSkel_of_stay hg]
    · rw [stepSkel_of_stay ht]
  · have hg' := closeAct_of_another_grain hne hg
    rw [stepSkel_of_stay (x := xs g') hg']
    rcases stepSkel_leaves_nothing_a_close_takes g g' now p (xs g) s with ht | ht
    · rw [ht, stepSkel_of_stay hg']
    · rw [stepSkel_of_stay ht]

/-! ### A close of one grain leaves another grain's child fold as it was

`foldFxOf g` reads the skeletons of the lines a close of grain `g` takes and nothing
else.  A close of another grain leaves every such line alone (`closeAct_of_another_grain`)
and puts nothing it moves where `g` takes from (`stepSkel_leaves_nothing_a_close_takes`),
so the fold `g` computes afterwards is the fold it computed before. -/

/-- The store's domain, the files, and — for grain `g` — every line's action and,
where `g` takes the line, its skeleton, all kept from `p` to `q`. -/
def SkelKept (g : Grain) (now : Day) (p q : PlanCore) : Prop :=
  q.store.dom = p.store.dom ∧ Frame p q ∧
    ∀ j, (q.store.get j).isSome = (p.store.get j).isSome ∧
      ∀ e f, p.store.get j = some e → q.store.get j = some f →
        closeAct g now q f.val.skel = closeAct g now p e.val.skel ∧
          (closeAct g now p e.val.skel ≠ .stay → f.val.skel = e.val.skel)

theorem SkelKept.filesLine_eq {g : Grain} {now : Day} {p q : PlanCore} (h : SkelKept g now p q) {j : Id}
    {e f : Entity} (he : p.store.get j = some e) (hf : q.store.get j = some f) :
    Tm.filesLine g now q f.val.skel = Tm.filesLine g now p e.val.skel := by
  unfold Tm.filesLine
  rw [((h.2.2 j).2 e f he hf).1]

theorem SkelKept.skel_of_files {g : Grain} {now : Day} {p q : PlanCore} (h : SkelKept g now p q) {j : Id}
    {e f : Entity} (he : p.store.get j = some e) (hf : q.store.get j = some f)
    (hfl : filesLine g now p e.val.skel = true) : f.val.skel = e.val.skel := by
  obtain ⟨r, hr⟩ := filesLine_iff.1 hfl
  exact ((h.2.2 j).2 e f he hf).2 (by rw [hr]; simp)

theorem SkelKept.get_none {g : Grain} {now : Day} {p q : PlanCore} (h : SkelKept g now p q) {j : Id} :
    q.store.get j = none ↔ p.store.get j = none := by
  have := (h.2.2 j).1
  cases hq : q.store.get j <;> cases hp : p.store.get j <;> simp_all

theorem foldParent_congr {g : Grain} {now : Day} {p q : PlanCore} (h : SkelKept g now p q) (j : Id) :
    foldParent g now q j = foldParent g now p j := by
  unfold foldParent
  split
  · rfl
  · cases hpj : p.store.get j with
    | none => rw [h.get_none.2 hpj]
    | some e =>
      cases hqj : q.store.get j with
      | none => rw [h.get_none.1 hqj] at hpj; cases hpj
      | some f =>
        simp only
        rw [h.filesLine_eq hpj hqj]
        cases hfl : filesLine g now p e.val.skel with
        | false => rfl
        | true =>
          simp only [if_true]
          have hsk := h.skel_of_files hpj hqj hfl
          have hpar : f.val.parent = e.val.parent := by
            show Field.parentRef f.val.skel.line = Field.parentRef e.val.skel.line
            rw [hsk]
          rw [hpar]
          cases e.val.parent with
          | none => rfl
          | some i =>
            simp only
            cases hpi : p.store.get i with
            | none => rw [h.get_none.2 hpi]
            | some ei =>
              cases hqi : q.store.get i with
              | none => rw [h.get_none.1 hqi] at hpi; cases hpi
              | some fi =>
                simp only
                rw [h.filesLine_eq hpi hqi]
                cases hfi : filesLine g now p ei.val.skel with
                | false => rfl
                | true =>
                  have hski := h.skel_of_files hpi hqi hfi
                  have hd1 : fi.val.live.doc = ei.val.live.doc := congrArg Skel.doc hski
                  have hd2 : f.val.live.doc = e.val.live.doc := congrArg Skel.doc hsk
                  rw [hd1, hd2]

theorem foldUp_congr {g : Grain} {now : Day} {p q : PlanCore} (h : SkelKept g now p q) :
    ∀ (n : Nat) (j : Id), foldUp g now q n j = foldUp g now p n j := by
  intro n
  induction n with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    unfold foldUp
    rw [foldParent_congr h j]
    cases foldParent g now p j with
    | none => rfl
    | some i => exact ih i

theorem dropsInto_congr {g : Grain} {now : Day} {p q : PlanCore} (h : SkelKept g now p q) (j : Id) :
    dropsInto g now q j = dropsInto g now p j := by
  unfold dropsInto
  rw [foldParent_congr h j, h.1]
  cases foldParent g now p j with
  | none => rfl
  | some i => exact foldUp_congr h _ i

theorem foldTab_congr {g : Grain} {now : Day} {bm : Nat} {p q : PlanCore} (h : SkelKept g now p q) :
    foldTab g now bm q = foldTab g now bm p := by
  unfold foldTab
  rw [h.1]
  congr 1
  funext j
  rw [dropsInto_congr h j]
  cases hd : dropsInto g now p j with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
    obtain ⟨_, _, _, ej, er, hj, _, hfj, _, _⟩ := dropsInto_spec hd
    unfold ownMinutes
    rw [hj]
    cases hqj : q.store.get j with
    | none => rw [h.get_none.1 hqj] at hj; cases hj
    | some f =>
      simp only
      have hsk := h.skel_of_files hj hqj hfj
      show remainingOf bm f.val.skel.line = remainingOf bm ej.val.skel.line
      rw [hsk]

/-- **The child fold is a function of what the close takes.** -/
theorem foldFxOf_congr {g : Grain} {now : Day} {bm : Nat} {p q : PlanCore} (h : SkelKept g now p q) :
    foldFxOf g now bm q = foldFxOf g now bm p := by
  funext i
  unfold foldFxOf foldFxIn
  rw [foldTab_congr h, dropsInto_congr h i]

theorem WfPlan.mapAt_dom {p q : WfPlan} {i : Id} {f : Entity → Except KErr Entity}
    (h : p.mapAt i f = .ok q) : q.val.store.dom = p.val.store.dom := by
  unfold WfPlan.mapAt at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · injection h with h
        subst h
        rfl
      · simp at h

theorem landAt_dom {p q : WfPlan} {k : DocIx} {spot : Option Nat} {i : Id}
    {f : Site → Entity → Except KErr Entity} (h : landAt p k spot i f = .ok q) :
    q.val.store.dom = p.val.store.dom := by
  cases spot with
  | none => exact WfPlan.mapAt_dom h
  | some n =>
    unfold landAt at h
    simp only at h
    cases h1 : p.shiftAt k n with
    | error x => simp [h1] at h
    | ok q1 =>
      simp only [h1] at h
      rw [WfPlan.mapAt_dom h, WfPlan.shiftAt_val h1]
      rfl

theorem closeOne_dom {g : Grain} {now : Day} {x : FoldFx} {i : Id} {p q : WfPlan}
    (h : closeOne g now x i p = .ok q) : q.val.store.dom = p.val.store.dom := by
  unfold closeOne at h
  split at h
  · simp at h
  · split at h
    · injection h with h; subst h; rfl
    · split at h
      · simp at h
      · exact landAt_dom h
    · split at h
      · exact WfPlan.mapAt_dom h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · exact landAt_dom (guardStray_ok h).1
    · split at h
      · simp at h
      · split at h
        · simp at h
        · exact landAt_dom h

/-- **A close keeps the store's domain**: it relocates and rewrites lines, and never
adds or removes an id. -/
theorem close_dom {g : Grain} {now : Day} {bm : Nat} {p q : WfPlan} (h : close g now bm p = .ok q) :
    q.val.store.dom = p.val.store.dom := by
  revert h
  show (closeCands g now p.val).foldlM (fun q i => closeOne g now (foldFxOf g now bm p.val i) i q) p = _ → _
  generalize foldFxOf g now bm p.val = fx
  generalize closeCands g now p.val = l
  induction l generalizing p with
  | nil => intro h; injection h with h; subst h; rfl
  | cons i rest ih =>
    simp only [List.foldlM_cons]
    cases h1 : closeOne g now (fx i) i p with
    | error x => intro h; cases h
    | ok p1 =>
      intro h
      exact (ih h).trans (closeOne_dom h1)

/-- **A close of one grain keeps what another grain's close takes.** -/
theorem close_keeps_skel_of_another_grain {g g' : Grain} {now : Day} {bm : Nat} {p q : WfPlan}
    (hne : g ≠ g') (h : close g now bm p = .ok q) : SkelKept g' now p.val q.val := by
  obtain ⟨hfr, hall⟩ := close_spec h
  refine ⟨close_dom h, hfr, fun j => ⟨?_, fun e f he hf => ?_⟩⟩
  · have hm := (hall j).1
    cases hq : q.val.store.get j <;> cases hp : p.val.store.get j <;> rw [hq, hp] at hm <;> simp_all
  · have hm := (hall j).1
    rw [he, hf] at hm
    simp only [Option.map_some, Option.some.injEq] at hm
    rw [closeAct_frame hfr, hm]
    by_cases hs : closeAct g now p.val e.val.skel = .stay
    · rw [stepSkel_of_stay hs]
      exact ⟨rfl, fun _ => rfl⟩
    · have hs' := closeAct_of_another_grain hne hs
      rcases stepSkel_leaves_nothing_a_close_takes g g' now p.val (foldFxOf g now bm p.val j) e.val.skel with
        ht | ht
      · rw [ht]; exact ⟨rfl, fun _ => rfl⟩
      · rw [ht, hs']; exact ⟨rfl, fun hc => absurd rfl hc⟩

theorem close_keeps_foldFxOf_of_another_grain {g g' : Grain} {now : Day} {bm bm' : Nat} {p q : WfPlan}
    (hne : g ≠ g') (h : close g now bm p = .ok q) : foldFxOf g' now bm' q.val = foldFxOf g' now bm' p.val :=
  foldFxOf_congr (close_keeps_skel_of_another_grain hne h)

/-- Two closes in sequence, per id: the skeleton is the second grain's step of
the first grain's step, both read against the *starting* plan's files and each with
the child fold its grain computes on the starting plan. -/
theorem close_bind_close_skel {g g' : Grain} {now : Day} {bm : Nat} {p q : WfPlan}
    (h : (close g now bm p).bind (close g' now bm) = .ok q) (j : Id) :
    (q.val.store.get j).map (fun e => e.val.skel) =
      (p.val.store.get j).map
        (fun e => stepSkel g' now p.val (foldFxOf g' now bm p.val j)
          (stepSkel g now p.val (foldFxOf g now bm p.val j) e.val.skel)) := by
  cases h1 : close g now bm p with
  | error x => rw [h1] at h; exact absurd h (by simp [Except.bind])
  | ok q1 =>
    rw [h1] at h
    have h2 : close g' now bm q1 = .ok q := h
    obtain ⟨hf1, hs1⟩ := close_spec h1
    have e2 := ((close_spec h2).2 j).1
    have e1 := (hs1 j).1
    rw [e2]
    cases hq1 : q1.val.store.get j with
    | none =>
      rw [hq1] at e1
      cases hp : p.val.store.get j with
      | none => rfl
      | some _ => rw [hp] at e1; simp at e1
    | some f1 =>
      rw [hq1] at e1
      cases hp : p.val.store.get j with
      | none => rw [hp] at e1; simp at e1
      | some e =>
        rw [hp] at e1
        simp only [Option.map_some, Option.some.injEq] at e1 ⊢
        rw [stepSkel_frame hf1, e1]
        apply stepSkel_congr_fx
        intro hne
        by_cases hgg : g = g'
        · subst hgg
          have := (hs1 j).2 f1 hq1
          rw [closeAct_frame hf1, e1] at this
          exact absurd this hne
        · rw [close_keeps_foldFxOf_of_another_grain hgg h1]

/-- **L17's commuting half.**  Closing two grains at the same instant, in either
order, leaves every id with the same skeleton — the same file, the same tombstone
file and bytes, the same box and the same bytes — whenever both orders succeed.
(For one grain twice the two orders are one expression; the content is at
distinct grains.)  Neither order sees the other's output, because every
destination is open and a dropped child is settled
(`stepSkel_leaves_nothing_a_close_takes`), and neither changes what the other's child
fold computes (`close_keeps_foldFxOf_of_another_grain`).  What this
does **not** say, and what is false (`close_week_and_close_month_do_not_commute`),
is that the two plans are equal: ranks in a shared destination depend on which
close landed first.  `close_week_month_orders_both_succeed_and_differ`
(Boundary.lean) exhibits both hypotheses, at week and month, on a loaded plan. -/
theorem two_closes_at_one_instant_commute_on_skeletons {g g' : Grain} {now : Day} {bm : Nat}
    {p q r : WfPlan}
    (hgg : (close g now bm p).bind (close g' now bm) = .ok q)
    (hgg' : (close g' now bm p).bind (close g now bm) = .ok r) (j : Id) :
    (q.val.store.get j).map (fun e => e.val.skel) =
      (r.val.store.get j).map (fun e => e.val.skel) := by
  by_cases hne : g = g'
  · subst hne
    rw [hgg] at hgg'
    injection hgg' with hqr
    rw [hqr]
  · rw [close_bind_close_skel hgg, close_bind_close_skel hgg']
    cases p.val.store.get j with
    | none => rfl
    | some e =>
      simp only [Option.map_some]
      exact congrArg some (stepSkel_comm g g' now p.val (fun g => foldFxOf g now bm p.val j) e.val.skel)

/-! ## `autoClose`: catch-up is one step per grain (stage 4 step 4)

§6.3: close "runs automatically on the first command after the period ends".
Fork-point `auto_close` ran it period by period, day by day, for at most
`AUTO_CLOSE_CATCHUP = 16` periods, each one filing into the successor of the
period it closed — so a tree more than sixteen days stale left its older day
files **unrun** (and the host's `closed` map said they were done), and a tree
fourteen days stale filed a day's leftovers into a week that the next iteration
then closed, stamping them twice.

With D1's target, every close files into a region containing *now*, which no
close at that instant takes from (`stepSkel_lands_outside_every_closed_region`).
So one close per grain takes **every** closed period of that grain at once —
`close g now` already folds over all of them — and nothing one grain files is
work for another.  There is no iteration count to get wrong: `autoClose` is the
three closes, finest first and coarsest last, and a refusal anywhere refuses the
whole call, so a period is never marked done without being run.

Which order is not a correctness choice: at one instant the grains commute on
every line's skeleton (`two_closes_at_one_instant_commute_on_skeletons`) and
differ only in the rank of lines landing in a shared section
(`close_week_and_close_month_do_not_commute`).  Coarsest last puts a week's
records ahead of the older month's carried ones in the open month's
`# Demoted` — the newer leftovers first. -/

/-- The grains `autoClose` closes, in the order it closes them. -/
def autoCloseOrder : List Grain := [day, week, month]

/-- The order is the containment chain walked up from its finest grain. -/
theorem autoCloseOrder_is_the_chain :
    autoCloseOrder = [day, coarsen day, coarsen (coarsen day)] := rfl

/-- Each grain once — not sixteen times, not zero times. -/
theorem autoCloseOrder_names_each_grain_once : ∀ g : Grain, autoCloseOrder.count g = 1 := by
  decide

/-- Finest first, coarsest last. -/
theorem autoCloseOrder_is_coarsest_last : autoCloseOrder.Pairwise (fun a b => a.val < b.val) := by
  decide

/-- **§6.3's automatic close, at one instant**: each grain's close once, in
`autoCloseOrder`.  The provisional `Goals.autoClose` signature, made real. -/
def autoClose (now : Day) (bm : Nat) : Transform := fun p =>
  autoCloseOrder.foldlM (fun q g => close g now bm q) p

/-- **L19a (discharged from `Goals.lean`, as stated).**  `autoClose` is exactly
"close each grain once, coarsest last": no loop, no bound, and no
`none`-versus-`some` case anywhere but inside each close's own candidate set. -/
theorem autoClose_is_each_grain_once (now : Day) (bm : Nat) (p : WfPlan) :
    autoClose now bm p
      = (close day now bm p).bind (fun q => (close week now bm q).bind (close month now bm)) := by
  show ([day, week, month] : List Grain).foldlM (fun q g => close g now bm q) p = _
  simp only [List.foldlM_cons, List.foldlM_nil]
  cases h1 : close day now bm p with
  | error x => rfl
  | ok q1 =>
    show (close week now bm q1 >>= fun q => close month now bm q >>= fun q' => pure q') =
      (close week now bm q1).bind (close month now bm)
    cases h2 : close week now bm q1 with
    | error x => rfl
    | ok q2 =>
      show (close month now bm q2 >>= fun q' => pure q') = close month now bm q2
      cases close month now bm q2 <;> rfl

/-- A successful `autoClose`, unpacked into its three closes. -/
theorem autoClose_ok {now : Day} {bm : Nat} {p q : WfPlan} (h : autoClose now bm p = .ok q) :
    ∃ q1 q2, close day now bm p = .ok q1 ∧ close week now bm q1 = .ok q2 ∧ close month now bm q2 = .ok q := by
  rw [autoClose_is_each_grain_once] at h
  cases h1 : close day now bm p with
  | error x => rw [h1] at h; exact absurd h (by simp [Except.bind])
  | ok q1 =>
    rw [h1] at h
    cases h2 : close week now bm q1 with
    | error x =>
      have h' : (close week now bm q1).bind (close month now bm) = .ok q := h
      rw [h2] at h'; exact absurd h' (by simp [Except.bind])
    | ok q2 =>
      have h' : (close week now bm q1).bind (close month now bm) = .ok q := h
      rw [h2] at h'
      exact ⟨q1, q2, rfl, h2, h'⟩

/-- **The check bites: a refusal refuses the whole call.**  If any of the three
closes refuses, `autoClose` returns that refusal — there is no plan in which
some grain was run and the rest were stamped done. -/
theorem autoClose_refuses_what_a_grain_refuses {now : Day} {bm : Nat} {p : WfPlan} {x : KErr}
    (h : autoClose now bm p = .error x) :
    close day now bm p = .error x ∨
      ∃ q1, close day now bm p = .ok q1 ∧
        (close week now bm q1 = .error x ∨
          ∃ q2, close week now bm q1 = .ok q2 ∧ close month now bm q2 = .error x) := by
  rw [autoClose_is_each_grain_once] at h
  cases h1 : close day now bm p with
  | error y => rw [h1] at h; exact Or.inl h
  | ok q1 =>
    rw [h1] at h
    refine Or.inr ⟨q1, rfl, ?_⟩
    have h' : (close week now bm q1).bind (close month now bm) = .error x := h
    cases h2 : close week now bm q1 with
    | error y => rw [h2] at h'; exact Or.inl h'
    | ok q2 => rw [h2] at h'; exact Or.inr ⟨q2, rfl, h'⟩

/-- Every close refusal reaches `autoClose` unchanged when it is the day's. -/
theorem autoClose_refuses_a_refused_day_close {now : Day} {bm : Nat} {p : WfPlan} {x : KErr}
    (h : close day now bm p = .error x) : autoClose now bm p = .error x := by
  rw [autoClose_is_each_grain_once, h]
  rfl

/-- No line of the plan is one a close of grain `g` at `now` would take. -/
def NothingToClose (g : Grain) (now : Day) (p : WfPlan) : Prop :=
  ∀ i f, p.val.store.get i = some f → closeAct g now p.val f.val.skel = .stay

/-- **A close of any grain leaves nothing new for a close of any other.**  What
the close moved lands outside every closed region, and what it did not move
kept its skeleton against unchanged files. -/
theorem close_keeps_nothing_to_close {g g' : Grain} {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close g' now bm p = .ok q) (hp : NothingToClose g now p) : NothingToClose g now q := by
  intro i f hq
  obtain ⟨hfr, hall⟩ := close_spec h
  have hm := (hall i).1
  rw [hq] at hm
  cases hpi : p.val.store.get i with
  | none => rw [hpi] at hm; simp at hm
  | some e =>
    rw [hpi] at hm
    simp only [Option.map_some, Option.some.injEq] at hm
    rw [closeAct_frame hfr, hm]
    rcases stepSkel_leaves_nothing_a_close_takes g' g now p.val (foldFxOf g' now bm p.val i) e.val.skel with
      ht | ht
    · rw [ht]; exact hp i e hpi
    · exact ht

/-- After a successful `autoClose`, no line is one a close of **any** grain at
that instant would take. -/
theorem autoClose_leaves_nothing_to_close {now : Day} {bm : Nat} {p q : WfPlan}
    (h : autoClose now bm p = .ok q) (g : Grain) : NothingToClose g now q := by
  obtain ⟨q1, q2, h1, h2, h3⟩ := autoClose_ok h
  have d1 : NothingToClose day now q1 := close_leaves_no_line_it_would_take h1
  have w2 : NothingToClose week now q2 := close_leaves_no_line_it_would_take h2
  have m3 : NothingToClose month now q := close_leaves_no_line_it_would_take h3
  have d3 := close_keeps_nothing_to_close h3 (close_keeps_nothing_to_close h2 d1)
  have w3 := close_keeps_nothing_to_close h3 w2
  rcases g with ⟨_ | _ | _ | n, hn⟩
  · exact d3
  · exact w3
  · exact m3
  · omega

/-- **F1 / L19b (discharged from `Goals.lean`, as stated).**  A tree however
stale catches up in one call and stays caught up: a second `autoClose` at the
same instant returns the plan unchanged.  There is no sixteen-period bound for
the first call to fall short of, and no "closed" record to get out of step with
the work — whether a period still needs closing is read off the plan.

This is the fold on `WfPlan` at one `now`, like L16 (`close_is_idempotent`), and
not §6.3's host-side `state.json` idempotence across invocations.
`the_stale_tree_catches_up_in_one_call` (Boundary.lean) satisfies the
hypothesis on a loaded plan three months stale. -/
theorem autoClose_catches_up_in_one_step (now : Day) (bm : Nat) (p q : WfPlan)
    (h : autoClose now bm p = .ok q) : autoClose now bm q = .ok q := by
  have hs := autoClose_leaves_nothing_to_close h
  rw [autoClose_is_each_grain_once,
    close_without_candidates_is_the_identity (closeCands_eq_nil_of_stay (hs day))]
  show (close week now bm q).bind (close month now bm) = _
  rw [close_without_candidates_is_the_identity (closeCands_eq_nil_of_stay (hs week))]
  exact close_without_candidates_is_the_identity (closeCands_eq_nil_of_stay (hs month))

/-- **Narrowed L19c** (`autoClose_runs_every_period_it_passes`, which says no
live line of any kind stays in a closed region, and is refuted in Boundary.lean
by the `[x]`, recurring and done-outcome lines §6.3 leaves behind).  After
`autoClose`, a line in a closed region of its file's own grain is settled or of
a box that grain's row does not take, recurring, or a wall that is already over:
**nothing unfinished is stranded, at any grain, however stale the tree** — the
owner's three-month case, where fork-point `auto_close` ran no day close at all. -/
theorem autoClose_strands_no_unfinished_line {now : Day} {bm : Nat} {p q : WfPlan}
    (h : autoClose now bm p = .ok q) (i : Id) (f : Entity)
    (hq : q.val.store.get i = some f) (r : Region)
    (hr : docRegion q.val f.val.live.doc = some r)
    (hkind : docKindAt q.val f.val.live.doc = kindOfGrain r.grain)
    (htakes : (closePolicy r.grain).takes f.val.status = true)
    (hrec : f.val.recur = Recur.none)
    (hwall : ∀ a b : DT, f.val.shape = Shape.interval a b → now ≤ b.day) :
    ¬ Closed r now := by
  intro hc
  have hst := autoClose_leaves_nothing_to_close h r.grain i f hq
  have hreg : closedRegionOf r.grain now q.val f.val.skel.doc = some r := by
    show closedRegionOf r.grain now q.val f.val.live.doc = some r
    unfold closedRegionOf
    rw [hr]
    simp [hkind, hc]
  have hrec' : f.val.skel.recurring = false := by
    show decide (Field.viewRecur f.val.line ≠ Recur.none) = false
    have : Field.viewRecur f.val.line = Recur.none := hrec
    simp [this]
  have htakes' : (closePolicy r.grain).takes f.val.skel.status = true := htakes
  have hwalls := (closePolicy_exemptions r.grain).2
  unfold closeAct at hst
  rw [hreg] at hst
  simp only [htakes', hrec', Bool.true_eq_false, Bool.false_eq_true, if_false] at hst
  split at hst
  · cases hst
  have hsh : ∀ a b : DT, Field.viewShape f.val.line = Shape.interval a b → now ≤ b.day := hwall
  revert hst
  show (match (match Field.viewShape f.val.line with
          | .interval _ b => some (decide (now ≤ b.day))
          | _ => none) with
        | some ahead => exemptAct (closePolicy r.grain).walls ahead
        | none => CloseAct.file r) = CloseAct.stay → False
  cases hv : Field.viewShape f.val.line with
  | interval a b =>
    have := hsh a b hv
    simp [this, hwalls, exemptAct]
  | none => simp
  | point _ => simp
  | window _ _ => simp

/-- Two closes' worth of skeleton bookkeeping, generalised: if every id's
skeleton is `F` of its skeleton in `p0`, one more close at grain `g` makes it
`stepSkel g` of that, read against `p0`'s files, with the child fold that close
computes on the plan it is handed. -/
theorem close_skel_after {g : Grain} {now : Day} {bm : Nat} {p0 p q : WfPlan} (F : Id → Skel → Skel)
    (hf0 : Frame p0.val p.val)
    (hpre : ∀ j, (p.val.store.get j).map (fun e => e.val.skel) =
      (p0.val.store.get j).map (fun e => F j e.val.skel))
    (h : close g now bm p = .ok q) :
    Frame p0.val q.val ∧ ∀ j, (q.val.store.get j).map (fun e => e.val.skel) =
      (p0.val.store.get j).map (fun e => stepSkel g now p0.val (foldFxOf g now bm p.val j) (F j e.val.skel)) := by
  obtain ⟨hfr, hall⟩ := close_spec h
  refine ⟨Frame.trans hf0 hfr, fun j => ?_⟩
  rw [(hall j).1]
  have e1 := hpre j
  cases hp : p.val.store.get j with
  | none =>
    rw [hp] at e1
    cases hp0 : p0.val.store.get j with
    | none => rfl
    | some _ => rw [hp0] at e1; simp at e1
  | some e =>
    rw [hp] at e1
    cases hp0 : p0.val.store.get j with
    | none => rw [hp0] at e1; simp at e1
    | some e0 =>
      rw [hp0] at e1
      simp only [Option.map_some, Option.some.injEq] at e1 ⊢
      rw [stepSkel_frame hf0, e1]

/-- **`autoClose`, per id**: three steps against the starting plan's files, each
with the child fold its grain computes on the starting plan — the day and month rows
fold nothing (`foldFxOf_of_asAnyLine`), and the day close leaves the week row's fold
as it was (`close_keeps_foldFxOf_of_another_grain`). -/
theorem autoClose_skel {now : Day} {bm : Nat} {p q : WfPlan} (h : autoClose now bm p = .ok q)
    {i : Id} {e f : Entity} (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) :
    f.val.skel = stepSkel month now p.val (foldFxOf month now bm p.val i)
      (stepSkel week now p.val (foldFxOf week now bm p.val i)
        (stepSkel day now p.val (foldFxOf day now bm p.val i) e.val.skel)) := by
  obtain ⟨q1, q2, h1, h2, h3⟩ := autoClose_ok h
  have s1 := close_skel_after (p0 := p) (fun _ s => s) (Frame.refl _)
    (fun j => by cases p.val.store.get j <;> rfl) h1
  have s2 := close_skel_after (fun j s => stepSkel day now p.val (foldFxOf day now bm p.val j) s) s1.1 s1.2 h2
  have s3 := close_skel_after
    (fun j s => stepSkel week now p.val (foldFxOf week now bm q1.val j)
      (stepSkel day now p.val (foldFxOf day now bm p.val j) s)) s2.1 s2.2 h3
  have := s3.2 i
  rw [hp, hq] at this
  simp only [Option.map_some, Option.some.injEq] at this
  rw [this, close_keeps_foldFxOf_of_another_grain (by decide) h1,
    foldFxOf_of_asAnyLine (g := month) rfl, foldFxOf_of_asAnyLine (g := month) rfl]

/-- Three grains' steps on one line are one grain's step: whichever step takes
the line puts it where no later grain takes it from, whatever each grain's child
fold asks. -/
theorem stepSkel_three_is_one (now : Day) (P : PlanCore) (xs : Grain → FoldFx) (s : Skel) :
    ∃ g : Grain, stepSkel month now P (xs month) (stepSkel week now P (xs week) (stepSkel day now P (xs day) s)) =
      stepSkel g now P (xs g) s := by
  rcases stepSkel_leaves_nothing_a_close_takes day week now P (xs day) s with h1 | h1
  · rw [h1]
    rcases stepSkel_leaves_nothing_a_close_takes week month now P (xs week) s with h2 | h2
    · rw [h2]; exact ⟨month, rfl⟩
    · rw [stepSkel_of_stay h2]; exact ⟨week, rfl⟩
  · rw [stepSkel_of_stay h1]
    rcases stepSkel_leaves_nothing_a_close_takes day month now P (xs day) s with h3 | h3
    · rw [h3]; exact ⟨month, rfl⟩
    · rw [stepSkel_of_stay h3]; exact ⟨day, rfl⟩

/-- **Each line is taken at most once by `autoClose`.**  Its skeleton afterwards
is one grain's step of what it was — never a day close's filing re-filed by the
week close, the fork-point double take of a tree fourteen days stale — with the
child fold that grain computes on the starting plan. -/
theorem autoClose_takes_each_line_at_most_once {now : Day} {bm : Nat} {p q : WfPlan}
    (h : autoClose now bm p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) :
    ∃ g : Grain, f.val.skel = stepSkel g now p.val (foldFxOf g now bm p.val i) e.val.skel := by
  obtain ⟨g, hg⟩ := stepSkel_three_is_one now p.val (fun g => foldFxOf g now bm p.val i) e.val.skel
  exact ⟨g, (autoClose_skel h hp hq).trans hg⟩

/-- One step, at any grain, keeps a line's stamps, appends one, or — merging a
line into its item's standing record (README gap 53) — writes fork-point
`merge_stamps` of the record's history, the line's and that one stamp, which can
put more than one stamp on a line that had none.  A dropped child keeps its stamps,
and the child fold's estimate touches no stamp.  (Named
`stepSkel_adds_at_most_one_stamp` until the stage-4 hardening repair; the name said
more than the statement.) -/
theorem stepSkel_appends_at_most_one_stamp_or_merges (g : Grain) (now : Day) (p : PlanCore)
    (x : FoldFx) (s : Skel) :
    (stepSkel g now p x s).stamps = s.stamps ∨
      ∃ st, (stepSkel g now p x s).stamps = s.stamps ++ [st] ∨
        ∃ tl, s.archLine = some tl ∧
          (stepSkel g now p x s).stamps = mergeStamps (stampsOfLine tl) s.stamps st := by
  have hset : ∀ (ss : List Stamp) (l : RawItem), ss ≠ [] →
      (Field.viewDemoted (Field.setDemoted ss l)).getD [] = ss := by
    intro ss l hne
    rw [Field.view_set_demoted _ _ hne]
    rfl
  cases hact : closeAct g now p s with
  | stay => exact Or.inl (by unfold stepSkel; rw [hact])
  | carry => exact Or.inl (by unfold stepSkel; rw [hact]; cases carryTarget now p <;> rfl)
  | overdue => exact Or.inl (by unfold stepSkel; rw [hact]; cases overdueTarget p <;> rfl)
  | file r =>
    cases hx : x.isDrop with
    | true => exact Or.inl (by rw [stepSkel_of_drop hact hx]; rfl)
    | false =>
      rw [stepSkel_of_file hact hx]
      cases closeTarget g now p with
      | none => exact Or.inl rfl
      | some k =>
        simp only
        unfold skelAfter
        cases (closePolicy g).disposition with
        | move => exact Or.inl rfl
        | moveReopening =>
          simp only
          unfold stampedLine
          cases closeStamp g r.ix with
          | none => exact Or.inl rfl
          | some st => exact Or.inr ⟨st, Or.inl (hset _ _ (by simp))⟩
        | copy =>
          cases closeStamp g r.ix with
          | none => exact Or.inl rfl
          | some st =>
            cases ha : s.archLine with
            | none =>
              refine Or.inr ⟨st, Or.inl ?_⟩
              show (Field.viewDemoted (Field.setDemoted (stampsOfLine s.line ++ [st]) _)).getD [] = _
              exact hset _ _ (by simp)
            | some tl =>
              refine Or.inr ⟨st, Or.inr ⟨tl, rfl, ?_⟩⟩
              show (Field.viewDemoted (Field.setDemoted (mergeStamps (stampsOfLine tl) (stampsOfLine s.line) st) _)).getD [] = _
              exact hset _ _
                (List.ne_nil_of_mem (((mergeStamps_spec _ _ _).2 st).2 (Or.inr (Or.inr rfl))))

/-- **F1's double stamp, ruled out** (restates
`autoClose_stamps_each_line_at_most_once`, whose two disjuncts a merged record
falsifies).  Across one `autoClose`, however stale the tree, a line keeps its
stamps, has one appended, or is merged into its item's standing record — whose
stamps are then the record's, the line's and that one stamp, each once
(`mergeStamps_spec`), so no merge writes a stamp twice either.  A merge can add
the record's history to the line (`autoClose_merges_m2s_stamps`: `[]` to
`W37,W36`), so this is not "at most one stamp added to the line"; it was named
`autoClose_adds_at_most_one_stamp_to_each_line` until the stage-4 hardening repair,
and the name said more than the statement. -/
theorem autoClose_appends_at_most_one_stamp_or_merges_each_line {now : Day} {bm : Nat} {p q : WfPlan}
    (h : autoClose now bm p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) :
    f.val.stamps = e.val.stamps ∨ ∃ st, f.val.stamps = e.val.stamps ++ [st] ∨
      ∃ t, e.val.archive = some t ∧ f.val.stamps = mergeStamps (stampsOfLine t.line) e.val.stamps st := by
  obtain ⟨g, hg⟩ := autoClose_takes_each_line_at_most_once h hp hq
  rw [← Core.skel_stamps, ← Core.skel_stamps, hg]
  rcases stepSkel_appends_at_most_one_stamp_or_merges g now p.val (foldFxOf g now bm p.val i) e.val.skel with
    h1 | ⟨st, h2 | ⟨tl, ha, h3⟩⟩
  · exact Or.inl h1
  · exact Or.inr ⟨st, Or.inl h2⟩
  · refine Or.inr ⟨st, Or.inr ?_⟩
    cases he : e.val.archive with
    | none => simp [Core.skel, he] at ha
    | some t =>
      have ht : t.line = tl := by simpa [Core.skel, he] using ha
      exact ⟨t, rfl, by rw [ht]; exact h3⟩

/-- **The old law, where it still holds as stated**: a line whose item has no
standing record gains at most one stamp, appended. -/
theorem autoClose_stamps_each_line_with_no_record_at_most_once {now : Day} {bm : Nat} {p q : WfPlan}
    (h : autoClose now bm p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f)
    (hrec : e.val.archive = none) :
    f.val.stamps = e.val.stamps ∨ ∃ st, f.val.stamps = e.val.stamps ++ [st] := by
  rcases autoClose_appends_at_most_one_stamp_or_merges_each_line h hp hq with h1 | ⟨st, h2 | ⟨t, ha, _⟩⟩
  · exact Or.inl h1
  · exact Or.inr ⟨st, h2⟩
  · rw [hrec] at ha; cases ha

/-! ## Gap 59: a close keeps source order (stage 4 step 8)

`closeCands` used to be `dom` filtered, and the loader builds `dom` in reverse,
so the fold took the lower of two lines first and the higher one landed after it
— every close inverted the rank of the lines it carried into one file or one
section (README gap 59).  `closeCands` now sorts by (document, rank), and this
section proves what that buys: `close_keeps_source_order`.

**The shape of the proof.**  One step moves the id it takes and, for a landing
inside a section, shifts every rank of the destination at or after the landing
spot up by one (`closeOne_moves`: every other line's placement is `Site.bump`ed,
the destination's prose is `Doc.bump`ed, the files a close takes from are not
touched).  A shift is strictly monotone (`shiftRank_lt_iff`), so it never
reorders two lines of one file (`fold_keeps_order_both`); it moves a section's
next heading with the lines below it (`landingSpot_bump`), so a line that landed
at the end of a section stays above the spot the next line of that section is
given (`fold_keeps_order_after_first`); and a line landing at the end of a file
is above nothing (`live_rank_lt_endRank`).  The fold takes the higher line first
because the candidate list is sorted (`closeCands_sorted`), which is the only
place the sort is used. -/

def rankBump : Option Nat → Nat → Nat
  | none,   r => r
  | some n, r => shiftRank n r

theorem shiftRank_lt_iff (n a b : Nat) : shiftRank n a < shiftRank n b ↔ a < b := by
  unfold shiftRank; split <;> split <;> omega

theorem rankBump_lt_iff (o : Option Nat) (a b : Nat) : rankBump o a < rankBump o b ↔ a < b := by
  cases o with
  | none => exact Iff.rfl
  | some n => exact shiftRank_lt_iff n a b

theorem shiftRank_min (n a b : Nat) : Nat.min (shiftRank n a) (shiftRank n b) = shiftRank n (Nat.min a b) := by
  unfold shiftRank
  simp only [Nat.min_def]
  repeat' split
  all_goals omega

def Site.bump (k : DocIx) (o : Option Nat) (s : Site) : Site :=
  if s.doc = k then ⟨s.doc, rankBump o s.rank⟩ else s

theorem Site.bump_doc (k : DocIx) (o : Option Nat) (s : Site) : (s.bump k o).doc = s.doc := by
  unfold Site.bump; split <;> rfl

theorem Site.bump_rank_of_doc {k : DocIx} (o : Option Nat) {s : Site} (h : s.doc = k) :
    (s.bump k o).rank = rankBump o s.rank := by
  unfold Site.bump; rw [if_pos h]

theorem Site.bump_of_ne {k : DocIx} (o : Option Nat) {s : Site} (h : s.doc ≠ k) : s.bump k o = s := by
  unfold Site.bump; rw [if_neg h]

theorem Site.bump_none (k : DocIx) (s : Site) : s.bump k none = s := by
  unfold Site.bump; split <;> rfl

theorem Site.bump_lt {k : DocIx} (o : Option Nat) {s t : Site} (h : s.doc = t.doc) :
    (s.bump k o).rank < (t.bump k o).rank ↔ s.rank < t.rank := by
  by_cases hs : s.doc = k
  · rw [Site.bump_rank_of_doc o hs, Site.bump_rank_of_doc o (h ▸ hs)]
    exact rankBump_lt_iff o _ _
  · rw [Site.bump_of_ne o hs, Site.bump_of_ne o (h ▸ hs)]

def Doc.bump : Option Nat → Doc → Doc
  | none,   d => d
  | some n, d => d.shiftFrom n

theorem inComment_shiftFrom (n : Nat) (ps : List (Nat × List Char)) (r : Nat) :
    inComment (ps.map (fun q => (shiftRank n q.1, q.2))) (shiftRank n r) = inComment ps r := by
  unfold inComment commentOpenFrom
  rw [List.filter_map, List.foldl_map]
  congr 1
  apply List.filter_congr
  intro q _
  simp only [Function.comp, decide_eq_decide]
  exact shiftRank_lt_iff n q.1 r

theorem liveHeading_shiftFrom (n : Nat) (d : Doc) (q : Nat × List Char) :
    liveHeading (d.shiftFrom n) (shiftRank n q.1, q.2) = liveHeading d q := by
  unfold liveHeading Doc.shiftFrom
  simp only
  rw [inComment_shiftFrom]

def loOk : Option Nat → Nat → Bool
  | none,   _ => true
  | some l, r => decide (l < r)

def fhaStep (live : Nat × List Char → Bool) (want : List Char → Bool) (lo : Option Nat)
    (acc : Option Nat) (q : Nat × List Char) : Option Nat :=
  if live q && want q.2 && loOk lo q.1 then
    match acc with
    | none   => some q.1
    | some b => some (Nat.min b q.1)
  else acc

theorem firstHeadingAbove_eq (d : Doc) (lo : Option Nat) (want : List Char → Bool) :
    firstHeadingAbove d lo want = d.prose.foldl (fhaStep (liveHeading d) want lo) none := by
  cases lo <;> rfl

theorem loOk_shift (n : Nat) (lo : Option Nat) (r : Nat) :
    loOk (lo.map (shiftRank n)) (shiftRank n r) = loOk lo r := by
  cases lo with
  | none => rfl
  | some l => simp only [Option.map_some, loOk, decide_eq_decide]; exact shiftRank_lt_iff n l r

theorem foldl_fhaStep_shift (n : Nat) (live live' : Nat × List Char → Bool)
    (hl : ∀ q, live' (shiftRank n q.1, q.2) = live q) (want : List Char → Bool) (lo : Option Nat) :
    ∀ (ps : List (Nat × List Char)) (acc : Option Nat),
      (ps.map (fun q => (shiftRank n q.1, q.2))).foldl (fhaStep live' want (lo.map (shiftRank n)))
          (acc.map (shiftRank n)) =
        (ps.foldl (fhaStep live want lo) acc).map (shiftRank n) := by
  intro ps
  induction ps with
  | nil => intro acc; rfl
  | cons q t ih =>
    intro acc
    simp only [List.map_cons, List.foldl_cons]
    rw [← ih]
    congr 1
    unfold fhaStep
    have hc : (live' (shiftRank n q.1, q.2) && want q.2 && loOk (lo.map (shiftRank n)) (shiftRank n q.1)) =
        (live q && want q.2 && loOk lo q.1) := by rw [hl, loOk_shift]
    simp only at hc ⊢
    rw [hc]
    by_cases hb : (live q && want q.2 && loOk lo q.1) = true
    · rw [if_pos hb, if_pos hb]
      cases acc with
      | none => rfl
      | some b => simp only [Option.map_some, shiftRank_min]
    · rw [if_neg hb, if_neg hb]

theorem firstHeadingAbove_bump (o : Option Nat) (d : Doc) (lo : Option Nat) (want : List Char → Bool) :
    firstHeadingAbove (Doc.bump o d) (lo.map (rankBump o)) want =
      (firstHeadingAbove d lo want).map (rankBump o) := by
  cases o with
  | none =>
    have h1 : ∀ x : Option Nat, x.map (rankBump none) = x := fun x => by cases x <;> rfl
    rw [h1, h1]; rfl
  | some n =>
    rw [firstHeadingAbove_eq, firstHeadingAbove_eq]
    exact foldl_fhaStep_shift n (liveHeading d) (liveHeading (d.shiftFrom n))
      (liveHeading_shiftFrom n d) want lo d.prose none

theorem landingSpot_bump {p q : PlanCore} {k : DocIx} (o : Option Nat)
    (hd : q.docs[k]? = (p.docs[k]?).map (Doc.bump o)) (l : Landing) (src : Option (List Char)) :
    landingSpot q k l src = (landingSpot p k l src).map (Option.map (rankBump o)) := by
  have h0 : ∀ (d : Doc) (w : List Char → Bool),
      firstHeadingAbove (Doc.bump o d) none w = (firstHeadingAbove d none w).map (rankBump o) :=
    fun d w => firstHeadingAbove_bump o d none w
  have h1 : ∀ (d : Doc) (h : Nat) (w : List Char → Bool),
      firstHeadingAbove (Doc.bump o d) (some (rankBump o h)) w =
        (firstHeadingAbove d (some h) w).map (rankBump o) :=
    fun d h w => firstHeadingAbove_bump o d (some h) w
  unfold landingSpot
  rw [hd]
  cases p.docs[k]? with
  | none => rfl
  | some d =>
    simp only [Option.map_some]
    cases l with
    | fileEnd => rfl
    | demotedSection =>
      simp only
      rw [h0]
      cases firstHeadingAbove d none (fun h => secKind h == SecKind.demoted) with
      | none => rfl
      | some h => simp only [Option.map_some]; rw [h1]; rfl
    | sameSection =>
      simp only
      cases src with
      | none => simp only; rw [h0]; rfl
      | some s =>
        simp only
        rw [h0]
        cases firstHeadingAbove d none (fun h => headingBody h == headingBody s) with
        | none => rfl
        | some h => simp only [Option.map_some]; rw [h1]; rfl
    | overdueSection =>
      simp only
      rw [h0]
      cases firstHeadingAbove d none (fun h => headingBody h == "Overdue".toList) with
      | none => rfl
      | some h => simp only [Option.map_some]; rw [h1]; rfl

theorem landingSpot_src (p : PlanCore) (k : DocIx) {l : Landing} (hl : l ≠ .sameSection)
    (s s' : Option (List Char)) : landingSpot p k l s = landingSpot p k l s' := by
  unfold landingSpot
  cases p.docs[k]? with
  | none => rfl
  | some d =>
    cases l with
    | fileEnd => rfl
    | demotedSection => rfl
    | sameSection => exact absurd rfl hl
    | overdueSection => rfl

theorem le_foldl_max_nat : ∀ (xs : List Nat) (a x : Nat), x ∈ xs → x ≤ xs.foldl Nat.max a := by
  intro xs
  induction xs with
  | nil => intro a x h; simp at h
  | cons y t ih =>
    intro a x h
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · have : ∀ (ys : List Nat) (b : Nat), b ≤ ys.foldl Nat.max b := by
        intro ys; induction ys with
        | nil => intro b; exact Nat.le_refl b
        | cons z u ihu => intro b; exact Nat.le_trans (Nat.le_max_left b z) (ihu _)
      exact Nat.le_trans (Nat.le_max_right a x) (this t _)
    · exact ih _ x h

theorem live_rank_lt_endRank {p : PlanCore} {i : Id} {e : Entity} (h : p.store.get i = some e) :
    e.val.live.rank < endRank p e.val.live.doc := by
  have hl : (⟨i, e.val.live, serializeItem i (glyphAt e.val e.val.live) e.val.line⟩ : Line) ∈ p.lines := by
    unfold PlanCore.lines
    refine List.mem_flatMap.2 ⟨i, (p.store.domSpec i).mpr (by rw [h]; rfl), ?_⟩
    rw [h]
    simp [render, renderCore]
  have hm : e.val.live.rank ∈ docRanks p e.val.live.doc := by
    unfold docRanks
    refine List.mem_append_right _ (List.mem_map.2 ⟨_, List.mem_filter.2 ⟨hl, by simp⟩, rfl⟩)
  exact Nat.lt_succ_of_le (le_foldl_max_nat _ 0 _ hm)


theorem docs_shiftIn_getElem? (p : PlanCore) (k n d : Nat) :
    (p.shiftIn k n).docs[d]? = if d = k then (p.docs[d]?).map (Doc.shiftFrom n) else p.docs[d]? := by
  unfold PlanCore.shiftIn
  simp only [List.getElem?_modify]
  by_cases h : d = k
  · subst h; simp
  · have h' : ¬ k = d := fun hc => h hc.symm
    simp [h', h]

/-- A file no close at `now` takes a line from. -/
def docOpenAt (now : Day) (p : PlanCore) (k : DocIx) : Prop :=
  ∀ r, docRegion p k = some r → ¬ Closed r now

theorem landAt_moves {p q : WfPlan} {k : DocIx} {spot : Option Nat} {i : Id}
    {f : Site → Entity → Except KErr Entity} (hf : ∀ t e e', f t e = .ok e' → e'.val.live = t)
    (h : landAt p k spot i f = .ok q) :
    (∀ j, j ≠ i → (q.val.store.get j).map (fun e => e.val.live) =
        (p.val.store.get j).map (fun e => e.val.live.bump k spot)) ∧
      (∀ d, q.val.docs[d]? = if d = k then (p.val.docs[d]?).map (Doc.bump spot) else p.val.docs[d]?) ∧
      ∃ f', q.val.store.get i = some f' ∧ f'.val.live = ⟨k, spot.getD (endRank p.val k)⟩ := by
  cases spot with
  | none =>
    unfold landAt at h
    obtain ⟨hd, hj, e, e', _, hfe, hq⟩ := WfPlan.mapAt_spec h
    refine ⟨fun j hji => ?_, fun d => ?_, e', hq, hf _ _ _ hfe⟩
    · rw [hj j hji]
      cases p.val.store.get j with
      | none => rfl
      | some x => simp only [Option.map_some, Site.bump_none]
    · rw [hd]
      split
      · cases p.val.docs[d]? <;> rfl
      · rfl
  | some n =>
    unfold landAt at h
    simp only at h
    cases h1 : p.shiftAt k n with
    | error x => simp [h1] at h
    | ok q1 =>
      simp only [h1] at h
      have hv := WfPlan.shiftAt_val h1
      obtain ⟨hd, hj, e1, e', _, hfe, hq⟩ := WfPlan.mapAt_spec h
      refine ⟨fun j hji => ?_, fun d => ?_, e', hq, hf _ _ _ hfe⟩
      · rw [hj j hji, hv]
        show ((p.val.store.get j).map (Entity.shiftIn k n)).map _ = _
        cases p.val.store.get j with
        | none => rfl
        | some x => rfl
      · rw [hd, hv, docs_shiftIn_getElem?]
        rfl

theorem closeAct_closed {g : Grain} {now : Day} {p : PlanCore} {s : Skel}
    (h : closeAct g now p s ≠ .stay) : ∃ r, docRegion p s.doc = some r ∧ Closed r now := by
  unfold closeAct closedRegionOf at h
  cases hr : docRegion p s.doc with
  | none => rw [hr] at h; exact absurd rfl h
  | some r =>
    rw [hr] at h
    by_cases hc : docKindAt p s.doc = kindOfGrain g ∧ r.grain = g ∧ Closed r now
    · exact ⟨r, rfl, hc.2.2⟩
    · simp only at h
      rw [if_neg hc] at h; exact absurd rfl h

theorem closeOne_moves {g : Grain} {now : Day} {x : FoldFx} {i : Id} {p q : WfPlan}
    (h : closeOne g now x i p = .ok q) :
    (q = p ∧ ∀ e, p.val.store.get i = some e → closeAct g now p.val e.val.skel = .stay) ∨
    (∃ e k spot, p.val.store.get i = some e ∧ docOpenAt now p.val k ∧
      (∀ j, j ≠ i → (q.val.store.get j).map (fun e => e.val.live) =
          (p.val.store.get j).map (fun e => e.val.live.bump k spot)) ∧
      (∀ d, q.val.docs[d]? = if d = k then (p.val.docs[d]?).map (Doc.bump spot) else p.val.docs[d]?) ∧
      (∃ f', q.val.store.get i = some f' ∧ f'.val.live = ⟨k, spot.getD (endRank p.val k)⟩) ∧
      (closeAct g now p.val e.val.skel = .carry → carryTarget now p.val = some k ∧ spot = none) ∧
      (∀ r, closeAct g now p.val e.val.skel = .file r → closeTarget g now p.val = some k ∧
          landingSpot p.val k (closePolicy g).landing (sectionAt p.val e.val.live) = .ok spot ∧
          x.isDrop = false) ∧
      (closeAct g now p.val e.val.skel = .overdue → overdueTarget p.val = some k ∧
          landingSpot p.val k .overdueSection (sectionAt p.val e.val.live) = .ok spot)) ∨
    (q.val.docs = p.val.docs ∧
      (∀ j, (q.val.store.get j).map (fun e => e.val.live) = (p.val.store.get j).map (fun e => e.val.live)) ∧
      ∃ e r, p.val.store.get i = some e ∧ closeAct g now p.val e.val.skel = .file r ∧ x.isDrop = true) := by
  unfold closeOne at h
  split at h
  · simp at h
  · rename_i e hget
    split at h
    · rename_i hact
      injection h with h
      subst h
      exact Or.inl ⟨rfl, fun e' he' => by rw [hget] at he'; injection he' with he'; subst he'; exact hact⟩
    · rename_i hact
      split at h
      · simp at h
      · rename_i k hk
        obtain ⟨hj, hd, hi⟩ := landAt_moves (fun t e e' hm => moveTo_live hm) h
        refine Or.inr (Or.inl ⟨e, k, none, hget, ?_, hj, hd, hi, fun _ => ⟨hk, rfl⟩, fun r hr => ?_, fun ho => ?_⟩)
        · obtain ⟨_, _, hreg⟩ := findDocIx_spec hk
          intro r hr
          rw [hreg] at hr
          injection hr with hr
          subst hr
          exact regionOf_is_open week now
        · rw [hact] at hr; exact absurd hr (by simp)
        · rw [hact] at ho; exact absurd ho (by simp)
    · rename_i r hact
      split at h
      · rename_i hx
        obtain ⟨hd, hj, e0, f', hget0, hdrop, hq⟩ := WfPlan.mapAt_spec h
        rw [hget] at hget0
        injection hget0 with hget0
        subst hget0
        refine Or.inr (Or.inr ⟨hd, fun j => ?_, e, r, hget, hact, hx⟩)
        by_cases hji : j = i
        · subst hji
          rw [hq, hget]
          simp only [Option.map_some, Option.some.injEq]
          exact (dropE_skel hdrop).2
        · rw [hj j hji]
      · rename_i hx
        split at h
        · simp at h
        · rename_i k hk
          split at h
          · simp at h
          · rename_i spot hspot
            obtain ⟨hj, hd, hi⟩ := landAt_moves (fun t e e' hm => (fileE_skel hm).2) (guardStray_ok h).1
            refine Or.inr (Or.inl ⟨e, k, spot, hget, ?_, hj, hd, hi, fun hc => ?_,
              fun r' hr => ⟨hk, hspot, by simpa using hx⟩, fun ho => ?_⟩)
            · obtain ⟨_, _, hreg⟩ := findDocIx_spec hk
              intro r hr
              rw [hreg] at hr
              injection hr with hr
              subst hr
              exact closeTo_target_is_open g now
            · rw [hact] at hc; exact absurd hc (by simp)
            · rw [hact] at ho; exact absurd ho (by simp)
    · rename_i hact
      split at h
      · simp at h
      · rename_i k hk
        split at h
        · simp at h
        · rename_i spot hspot
          obtain ⟨hj, hd, hi⟩ := landAt_moves (fun t e e' hm => moveTo_live hm) h
          refine Or.inr (Or.inl ⟨e, k, spot, hget, ?_, hj, hd, hi, fun hc => ?_, fun r hr => ?_,
            fun _ => ⟨hk, hspot⟩⟩)
          · obtain ⟨_, _, hreg⟩ := overdueTarget_spec hk
            intro r hr
            rw [hreg] at hr
            cases hr
          · rw [hact] at hc; exact absurd hc (by simp)
          · rw [hact] at hr; exact absurd hr (by simp)


theorem carryTarget_frame {p q : PlanCore} (hf : Frame p q) (now : Day) :
    carryTarget now q = carryTarget now p := by
  unfold carryTarget; exact findDocIx_frame hf _ _

theorem closeTarget_frame {p q : PlanCore} (hf : Frame p q) (g : Grain) (now : Day) :
    closeTarget g now q = closeTarget g now p := by
  unfold closeTarget; exact findDocIx_frame hf _ _

theorem landingSpot_docs {p q : PlanCore} {k : DocIx} (h : q.docs[k]? = p.docs[k]?)
    (l : Landing) (src : Option (List Char)) : landingSpot q k l src = landingSpot p k l src := by
  unfold landingSpot; rw [h]

theorem sectionAt_docs {p q : PlanCore} {s : Site} (h : q.docs[s.doc]? = p.docs[s.doc]?) :
    sectionAt q s = sectionAt p s := by
  unfold sectionAt; rw [h]

theorem get_of_map_eq_some {q : WfPlan} {j : Id} {β : Type} {F : Entity → β} {x : β}
    (h : (q.val.store.get j).map F = some x) : ∃ b, q.val.store.get j = some b ∧ F b = x := by
  cases hq : q.val.store.get j with
  | none => rw [hq] at h; simp at h
  | some b => rw [hq] at h; simp only [Option.map_some, Option.some.injEq] at h; exact ⟨b, rfl, h⟩

/-- The docs no close at `now` takes from are untouched between `p0` and `P`. -/
def ClosedDocsKept (now : Day) (p0 P : PlanCore) : Prop :=
  ∀ d r, docRegion p0 d = some r → Closed r now → P.docs[d]? = p0.docs[d]?

/-- One step, seen from a line it did not take and whose file is closed. -/
theorem closeOne_keeps_untaken {g : Grain} {now : Day} {y : FoldFx} {c : Id} {p0 P P1 : WfPlan}
    (h1 : closeOne g now y c P = .ok P1) (hfr : Frame p0.val P.val) (hcd : ClosedDocsKept now p0.val P.val)
    {x : Id} (hx : x ≠ c) {ex b : Entity} (hb : P.val.store.get x = some b) (hbs : b.val.skel = ex.val.skel)
    (hbl : b.val.live = ex.val.live) {r : Region} (hr : docRegion p0.val ex.val.live.doc = some r)
    (hc : Closed r now) :
    Frame p0.val P1.val ∧ ClosedDocsKept now p0.val P1.val ∧
      ∃ b', P1.val.store.get x = some b' ∧ b'.val.skel = ex.val.skel ∧ b'.val.live = ex.val.live := by
  obtain ⟨hf1, hsk, _⟩ := closeOne_spec h1
  have hfr1 := hfr.trans hf1
  rcases closeOne_moves h1 with ⟨rfl, _⟩ | ⟨e, k, spot, _, hopen, hjs, hds, _, _, _⟩ | ⟨hdocs, hlives, _⟩
  · exact ⟨hfr, hcd, b, hb, hbs, hbl⟩
  · have hne : ∀ d r, docRegion p0.val d = some r → Closed r now → d ≠ k := by
      intro d r hr hc hdk
      subst hdk
      exact hopen r (by rw [hfr.2.2]; exact hr) hc
    refine ⟨hfr1, fun d r hr hc => ?_, ?_⟩
    · rw [hds d, if_neg (hne d r hr hc)]; exact hcd d r hr hc
    · have hs := hsk x hx
      rw [hb] at hs
      obtain ⟨b', hb', hb's⟩ := get_of_map_eq_some hs
      refine ⟨b', hb', hb's.trans hbs, ?_⟩
      have hl := hjs x hx
      rw [hb, hb'] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      rw [hl, hbl]
      exact Site.bump_of_ne spot (hne _ r hr hc)
  · refine ⟨hfr1, fun d r hr hc => by rw [hdocs]; exact hcd d r hr hc, ?_⟩
    have hs := hsk x hx
    rw [hb] at hs
    obtain ⟨b', hb', hb's⟩ := get_of_map_eq_some hs
    refine ⟨b', hb', hb's.trans hbs, ?_⟩
    have hl := hlives x
    rw [hb, hb'] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    rw [hl, hbl]

theorem fold_keeps_order_both (g : Grain) (now : Day) (fx : Id → FoldFx) (i j : Id) :
    ∀ (l : List Id) (P Q : WfPlan), l.foldlM (fun q c => closeOne g now (fx c) c q) P = .ok Q →
      i ∉ l → j ∉ l →
      (∃ a b, P.val.store.get i = some a ∧ P.val.store.get j = some b ∧
        a.val.live.doc = b.val.live.doc ∧ a.val.live.rank < b.val.live.rank) →
      ∃ a b, Q.val.store.get i = some a ∧ Q.val.store.get j = some b ∧
        a.val.live.doc = b.val.live.doc ∧ a.val.live.rank < b.val.live.rank := by
  intro l
  induction l with
  | nil =>
    intro P Q h _ _ hab
    simp only [List.foldlM_nil] at h
    injection h with h
    subst h
    exact hab
  | cons c rest ih =>
    intro P Q h hi hj hab
    simp only [List.foldlM_cons] at h
    cases h1 : closeOne g now (fx c) c P with
    | error x => rw [h1] at h; simp [bind, Except.bind] at h
    | ok P1 =>
      rw [h1] at h
      simp only [bind, Except.bind] at h
      have hci : i ≠ c := fun hc => hi (hc ▸ List.mem_cons_self ..)
      have hcj : j ≠ c := fun hc => hj (hc ▸ List.mem_cons_self ..)
      refine ih P1 Q h (fun hm => hi (List.mem_cons_of_mem _ hm)) (fun hm => hj (List.mem_cons_of_mem _ hm)) ?_
      obtain ⟨a, b, ha, hb, hd, hr⟩ := hab
      rcases closeOne_moves h1 with ⟨rfl, _⟩ | ⟨e, k, spot, _, _, hjs, _, _, _, _⟩ | ⟨_, hlives, _⟩
      · exact ⟨a, b, ha, hb, hd, hr⟩
      · have hli := hjs i hci
        have hlj := hjs j hcj
        rw [ha] at hli
        rw [hb] at hlj
        obtain ⟨a', ha', hal⟩ := get_of_map_eq_some hli
        obtain ⟨b', hb', hbl⟩ := get_of_map_eq_some hlj
        refine ⟨a', b', ha', hb', ?_, ?_⟩
        · simp only at hal hbl
          rw [hal, hbl, Site.bump_doc, Site.bump_doc, hd]
        · simp only at hal hbl
          rw [hal, hbl]
          exact (Site.bump_lt spot hd).2 hr
      · have hli := hlives i
        have hlj := hlives j
        rw [ha] at hli
        rw [hb] at hlj
        obtain ⟨a', ha', hal⟩ := get_of_map_eq_some hli
        obtain ⟨b', hb', hbl⟩ := get_of_map_eq_some hlj
        simp only at hal hbl
        exact ⟨a', b', ha', hb', by rw [hal, hbl, hd], by rw [hal, hbl]; exact hr⟩


theorem closeAct_skel_frame {g : Grain} {now : Day} {p0 P : PlanCore} (hfr : Frame p0 P) {b ex : Entity}
    (hbs : b.val.skel = ex.val.skel) : closeAct g now P b.val.skel = closeAct g now p0 ex.val.skel := by
  rw [closeAct_frame hfr, hbs]

/-- One step's landing keeps an earlier line of file `K` strictly above every spot
a later landing in `K` would name, at whichever landing that is. -/
theorem spot_bound_after_step {P P1 : WfPlan} {K k : DocIx} {spot : Option Nat} {L : Landing}
    {src : Option (List Char)} {a a' : Entity}
    (hds : ∀ d, P1.val.docs[d]? = if d = k then (P.val.docs[d]?).map (Doc.bump spot) else P.val.docs[d]?)
    (hal : a'.val.live = a.val.live.bump k spot) (had : a.val.live.doc = K)
    (hspot : ∀ s0, landingSpot P.val K L src = .ok s0 → ∀ n, s0 = some n → a.val.live.rank < n) :
    ∀ s1, landingSpot P1.val K L src = .ok s1 → ∀ n, s1 = some n → a'.val.live.rank < n := by
  intro spot' hsp' n hn
  by_cases hK : K = k
  · subst hK
    have hdk : P1.val.docs[K]? = (P.val.docs[K]?).map (Doc.bump spot) := by
      rw [hds K, if_pos rfl]
    rw [landingSpot_bump spot hdk] at hsp'
    cases hs0 : landingSpot P.val K L src with
    | error x => rw [hs0] at hsp'; simp [Except.map] at hsp'
    | ok s0 =>
      rw [hs0] at hsp'
      simp only [Except.map, Except.ok.injEq] at hsp'
      rw [hn] at hsp'
      cases s0 with
      | none => simp at hsp'
      | some n0 =>
        simp only [Option.map_some, Option.some.injEq] at hsp'
        rw [← hsp', hal, Site.bump_rank_of_doc _ had]
        exact (rankBump_lt_iff spot _ _).2 (hspot (some n0) hs0 n0 rfl)
  · have hdk : P1.val.docs[K]? = P.val.docs[K]? := by rw [hds K, if_neg hK]
    rw [landingSpot_docs hdk] at hsp'
    rw [hal, Site.bump_of_ne spot (by rw [had]; exact hK)]
    exact hspot spot' hsp' n hn

/-- A line of file `K` above the spot a landing names stays above the line that
lands there. -/
theorem rank_lt_landing {P : WfPlan} {K : DocIx} {spot : Option Nat} {a : Entity} {i : Id}
    (hPa : P.val.store.get i = some a) (had : a.val.live.doc = K)
    (hlt : ∀ n, spot = some n → a.val.live.rank < n) :
    (a.val.live.bump K spot).rank < spot.getD (endRank P.val K) := by
  cases spot with
  | none =>
    rw [Site.bump_none, ← had]
    exact live_rank_lt_endRank hPa
  | some m =>
    have hm := hlt m rfl
    rw [Site.bump_rank_of_doc _ had]
    show shiftRank m a.val.live.rank < m
    unfold shiftRank
    rw [if_neg (Nat.not_le.2 hm)]
    exact hm

/-- The line that landed at a spot is above every spot the next landing at the
same landing names. -/
theorem landed_rank_lt_next_spot {P P1 : WfPlan} {k : DocIx} {spot : Option Nat} {L : Landing}
    {src : Option (List Char)}
    (hds : ∀ d, P1.val.docs[d]? = if d = k then (P.val.docs[d]?).map (Doc.bump spot) else P.val.docs[d]?)
    (hsp : landingSpot P.val k L src = .ok spot) :
    ∀ s1, landingSpot P1.val k L src = .ok s1 → ∀ n, s1 = some n → spot.getD (endRank P.val k) < n := by
  intro spot' hsp' n hn
  have hdk : P1.val.docs[k]? = (P.val.docs[k]?).map (Doc.bump spot) := by
    rw [hds k, if_pos rfl]
  rw [landingSpot_bump spot hdk, hsp] at hsp'
  simp only [Except.map, Except.ok.injEq] at hsp'
  rw [hn] at hsp'
  cases spot with
  | none => simp at hsp'
  | some m =>
    simp only [Option.map_some, Option.some.injEq] at hsp'
    rw [← hsp']
    show m < shiftRank m m
    unfold shiftRank
    rw [if_pos (Nat.le_refl m)]
    exact Nat.lt_succ_self m

/-- **The fold, after the earlier line `i` has landed and before `j` does.**
`i` sits in the destination `K`, strictly before any rank `j`'s own landing
spot would name — at the row's landing for a filed line, at `# Overdue` for an
overdue one (D7).  `j` is filed forward, not dropped (B3's repair). -/
theorem fold_keeps_order_after_first (g : Grain) (now : Day) (fx : Id → FoldFx) (p0 : WfPlan) (i j : Id)
    (ej : Entity) (K : DocIx) (hact : closeAct g now p0.val ej.val.skel ≠ .stay)
    (hcarry : closeAct g now p0.val ej.val.skel = .carry → carryTarget now p0.val = some K)
    (hfile : ∀ r, closeAct g now p0.val ej.val.skel = .file r → closeTarget g now p0.val = some K)
    (hover : closeAct g now p0.val ej.val.skel = .overdue → overdueTarget p0.val = some K)
    (hxj : ∀ r, closeAct g now p0.val ej.val.skel = .file r → (fx j).isDrop = false) :
    ∀ (l : List Id) (P Q : WfPlan), l.foldlM (fun q c => closeOne g now (fx c) c q) P = .ok Q →
      l.Nodup → i ∉ l → j ∈ l → Frame p0.val P.val → ClosedDocsKept now p0.val P.val →
      (∃ b, P.val.store.get j = some b ∧ b.val.skel = ej.val.skel ∧ b.val.live = ej.val.live) →
      (∃ a, P.val.store.get i = some a ∧ a.val.live.doc = K ∧
        (∀ r, closeAct g now p0.val ej.val.skel = .file r → ∀ spot,
          landingSpot P.val K (closePolicy g).landing (sectionAt p0.val ej.val.live) = .ok spot →
          ∀ n, spot = some n → a.val.live.rank < n) ∧
        (closeAct g now p0.val ej.val.skel = .overdue → ∀ spot,
          landingSpot P.val K .overdueSection (sectionAt p0.val ej.val.live) = .ok spot →
          ∀ n, spot = some n → a.val.live.rank < n)) →
      ∃ a b, Q.val.store.get i = some a ∧ Q.val.store.get j = some b ∧
        a.val.live.doc = b.val.live.doc ∧ a.val.live.rank < b.val.live.rank := by
  obtain ⟨r0, hr0, hc0⟩ := closeAct_closed hact
  intro l
  induction l with
  | nil => intro _ _ _ _ _ hj; simp at hj
  | cons c rest ih =>
    intro P Q h hnd hi hj hfr hcd hb ha
    simp only [List.foldlM_cons] at h
    cases h1 : closeOne g now (fx c) c P with
    | error x => rw [h1] at h; simp [bind, Except.bind] at h
    | ok P1 =>
      rw [h1] at h
      simp only [bind, Except.bind] at h
      have hnd' := List.nodup_cons.1 hnd
      have hci : i ≠ c := fun hc => hi (hc ▸ List.mem_cons_self ..)
      obtain ⟨b, hPb, hbs, hbl⟩ := hb
      obtain ⟨a, hPa, had, hspot, hspotO⟩ := ha
      obtain ⟨hf1, _, _⟩ := closeOne_spec h1
      have hfr1 := hfr.trans hf1
      by_cases hjc : j = c
      · -- the step that lands `j`
        subst hjc
        refine fold_keeps_order_both g now fx i j rest P1 Q h
          (fun hm => hi (List.mem_cons_of_mem _ hm)) hnd'.1 ?_
        have hactP := closeAct_skel_frame (g := g) (now := now) hfr hbs
        rcases closeOne_moves h1 with ⟨_, hst⟩ |
            ⟨e, k, spot, hPe, _, hjs, _, ⟨f', hf', hlive⟩, hcar, hfil, hovr⟩ | ⟨_, _, e, r, hPe, hA, hx⟩
        · exact absurd ((hactP.symm.trans (hst b hPb))) hact
        · rw [hPb] at hPe
          injection hPe with hPe
          subst hPe
          have hli := hjs i hci
          rw [hPa] at hli
          obtain ⟨a', ha', hal⟩ := get_of_map_eq_some hli
          simp only at hal
          have hsec : sectionAt P.val b.val.live = sectionAt p0.val ej.val.live := by
            rw [hbl]; exact sectionAt_docs (hcd _ r0 hr0 hc0)
          have hkK : K = k ∧ ∀ n, spot = some n → a.val.live.rank < n := by
            cases hA : closeAct g now p0.val ej.val.skel with
            | stay => exact absurd hA hact
            | carry =>
              obtain ⟨hk, hsp⟩ := hcar (hactP.trans hA)
              rw [carryTarget_frame hfr, hcarry hA] at hk
              injection hk with hk
              exact ⟨hk, fun n hn => by rw [hsp] at hn; cases hn⟩
            | file r =>
              obtain ⟨hk, hsp, _⟩ := hfil r (hactP.trans hA)
              rw [closeTarget_frame hfr, hfile r hA] at hk
              injection hk with hk
              rw [hsec, ← hk] at hsp
              exact ⟨hk, fun n hn => hspot r hA spot hsp n hn⟩
            | overdue =>
              obtain ⟨hk, hsp⟩ := hovr (hactP.trans hA)
              rw [overdueTarget_frame hfr, hover hA] at hk
              injection hk with hk
              rw [hsec, ← hk] at hsp
              exact ⟨hk, fun n hn => hspotO hA spot hsp n hn⟩
          obtain ⟨hkK, hlt⟩ := hkK
          refine ⟨a', f', ha', hf', ?_, ?_⟩
          · rw [hal, Site.bump_doc, hlive, had, hkK]
          · rw [hal, hlive]
            rw [← hkK]
            exact rank_lt_landing hPa had hlt
        · rw [hPb] at hPe
          injection hPe with hPe
          subst hPe
          have hx' := hxj r (hactP.symm.trans hA)
          rw [hx] at hx'
          cases hx'
      · -- a step that lands some other line
        have hjr : j ∈ rest := (List.mem_cons.1 hj).resolve_left hjc
        obtain ⟨_, hcd1, b', hb', hb's, hb'l⟩ :=
          closeOne_keeps_untaken h1 hfr hcd hjc hPb hbs hbl hr0 hc0
        refine ih P1 Q h hnd'.2 (fun hm => hi (List.mem_cons_of_mem _ hm)) hjr hfr1 hcd1
          ⟨b', hb', hb's, hb'l⟩ ?_
        rcases closeOne_moves h1 with ⟨rfl, _⟩ | ⟨e, k, spot, _, hopen, hjs, hds, _, _, _, _⟩ |
            ⟨hdocs, hlives, _⟩
        · exact ⟨a, hPa, had, hspot, hspotO⟩
        · have hli := hjs i hci
          rw [hPa] at hli
          obtain ⟨a', ha', hal⟩ := get_of_map_eq_some hli
          simp only at hal
          exact ⟨a', ha', by rw [hal, Site.bump_doc, had],
            fun r hA => spot_bound_after_step hds hal had (hspot r hA),
            fun hA => spot_bound_after_step hds hal had (hspotO hA)⟩
        · have hli := hlives i
          rw [hPa] at hli
          obtain ⟨a', ha', hal⟩ := get_of_map_eq_some hli
          simp only at hal
          have hdk : P1.val.docs[K]? = P.val.docs[K]? := by rw [hdocs]
          refine ⟨a', ha', by rw [hal, had], fun r hA spot hsp n hn => ?_, fun hA spot hsp n hn => ?_⟩
          · rw [landingSpot_docs hdk] at hsp
            rw [hal]; exact hspot r hA spot hsp n hn
          · rw [landingSpot_docs hdk] at hsp
            rw [hal]; exact hspotO hA spot hsp n hn

/-- **The fold, for a line it drops** (B3's repair): a dropped child stays where it
is, so a line of its file above it — which no step of the fold moves, its file being
closed — stays above it. -/
theorem fold_keeps_order_of_drop (g : Grain) (now : Day) (fx : Id → FoldFx) (p0 : WfPlan) (i j : Id)
    (ej : Entity) {r0 : Region} (hactj : closeAct g now p0.val ej.val.skel = .file r0)
    (hxj : (fx j).isDrop = true) :
    ∀ (l : List Id) (P Q : WfPlan), l.foldlM (fun q c => closeOne g now (fx c) c q) P = .ok Q →
      l.Nodup → i ∉ l → j ∈ l → Frame p0.val P.val → ClosedDocsKept now p0.val P.val →
      (∃ b, P.val.store.get j = some b ∧ b.val.skel = ej.val.skel ∧ b.val.live = ej.val.live) →
      (∃ a, P.val.store.get i = some a ∧ a.val.live.doc = ej.val.live.doc ∧
        a.val.live.rank < ej.val.live.rank) →
      ∃ a b, Q.val.store.get i = some a ∧ Q.val.store.get j = some b ∧
        a.val.live.doc = b.val.live.doc ∧ a.val.live.rank < b.val.live.rank := by
  obtain ⟨r1, hr1, hc1⟩ := closeAct_closed (show closeAct g now p0.val ej.val.skel ≠ .stay by rw [hactj]; simp)
  intro l
  induction l with
  | nil => intro _ _ _ _ _ hj; simp at hj
  | cons c rest ih =>
    intro P Q h hnd hi hj hfr hcd hb ha
    simp only [List.foldlM_cons] at h
    cases h1 : closeOne g now (fx c) c P with
    | error x => rw [h1] at h; simp [bind, Except.bind] at h
    | ok P1 =>
      rw [h1] at h
      simp only [bind, Except.bind] at h
      have hnd' := List.nodup_cons.1 hnd
      have hci : i ≠ c := fun hc => hi (hc ▸ List.mem_cons_self ..)
      obtain ⟨b, hPb, hbs, hbl⟩ := hb
      obtain ⟨a, hPa, had, hlt⟩ := ha
      obtain ⟨hf1, _, _⟩ := closeOne_spec h1
      have hfr1 := hfr.trans hf1
      have hra : docRegion p0.val a.val.live.doc = some r1 := by rw [had]; exact hr1
      obtain ⟨_, hcd1, a', ha', _, ha'l⟩ :=
        closeOne_keeps_untaken (ex := a) h1 hfr hcd hci hPa rfl rfl hra hc1
      by_cases hjc : j = c
      · subst hjc
        have hactP := closeAct_skel_frame (g := g) (now := now) hfr hbs
        rcases closeOne_moves h1 with ⟨_, hst⟩ | ⟨_, _, _, hPe, _, _, _, _, _, hfil, _⟩ |
            ⟨_, hlives, _⟩
        · exact absurd (hactP.symm.trans (hst b hPb)) (by rw [hactj]; simp)
        · rw [hPb] at hPe
          injection hPe with hPe
          subst hPe
          have := (hfil r0 (hactP.trans hactj)).2.2
          rw [hxj] at this
          cases this
        · refine fold_keeps_order_both g now fx i j rest P1 Q h
            (fun hm => hi (List.mem_cons_of_mem _ hm)) hnd'.1 ?_
          have hlj := hlives j
          rw [hPb] at hlj
          obtain ⟨b', hb', hbl'⟩ := get_of_map_eq_some hlj
          simp only at hbl'
          exact ⟨a', b', ha', hb', by rw [ha'l, hbl', hbl, had], by rw [ha'l, hbl', hbl]; exact hlt⟩
      · have hjr : j ∈ rest := (List.mem_cons.1 hj).resolve_left hjc
        obtain ⟨_, _, b', hb', hb's, hb'l⟩ :=
          closeOne_keeps_untaken h1 hfr hcd hjc hPb hbs hbl hr1 hc1
        exact ih P1 Q h hnd'.2 (fun hm => hi (List.mem_cons_of_mem _ hm)) hjr hfr1 hcd1
          ⟨b', hb', hb's, hb'l⟩ ⟨a', ha', by rw [ha'l, had], by rw [ha'l]; exact hlt⟩

/-- **The fold, before either line has landed.**  The two lines are taken by the
same action, and the child fold drops both or neither. -/
theorem fold_keeps_order (g : Grain) (now : Day) (fx : Id → FoldFx) (p0 : WfPlan) (i j : Id) (ei ej : Entity)
    (hne : closeAct g now p0.val ei.val.skel ≠ .stay)
    (hact : closeAct g now p0.val ej.val.skel = closeAct g now p0.val ei.val.skel)
    (hfold : (fx j).isDrop = (fx i).isDrop)
    (hsec : closeAct g now p0.val ei.val.skel ≠ .carry → (closePolicy g).landing = .sameSection →
      sectionAt p0.val ei.val.live = sectionAt p0.val ej.val.live) :
    ∀ (l : List Id) (P Q : WfPlan), l.foldlM (fun q c => closeOne g now (fx c) c q) P = .ok Q →
      l.Nodup → [i, j].Sublist l → Frame p0.val P.val → ClosedDocsKept now p0.val P.val →
      (∃ a, P.val.store.get i = some a ∧ a.val.skel = ei.val.skel ∧ a.val.live = ei.val.live) →
      (∃ b, P.val.store.get j = some b ∧ b.val.skel = ej.val.skel ∧ b.val.live = ej.val.live) →
      ei.val.live.doc = ej.val.live.doc → ei.val.live.rank < ej.val.live.rank →
      ∃ a b, Q.val.store.get i = some a ∧ Q.val.store.get j = some b ∧
        a.val.live.doc = b.val.live.doc ∧ a.val.live.rank < b.val.live.rank := by
  have hnej : closeAct g now p0.val ej.val.skel ≠ .stay := by rw [hact]; exact hne
  obtain ⟨ri, hri, hci⟩ := closeAct_closed hne
  obtain ⟨rj, hrj, hcj⟩ := closeAct_closed hnej
  intro l
  induction l with
  | nil => intro _ _ _ _ hs; simp at hs
  | cons c rest ih =>
    intro P Q h hnd hs hfr hcd ha hb hdoc hlt
    simp only [List.foldlM_cons] at h
    cases h1 : closeOne g now (fx c) c P with
    | error x => rw [h1] at h; simp [bind, Except.bind] at h
    | ok P1 =>
      rw [h1] at h
      simp only [bind, Except.bind] at h
      have hnd' := List.nodup_cons.1 hnd
      have hij : i ≠ j := by
        have := (hnd.sublist hs)
        simp at this
        exact this
      obtain ⟨a, hPa, has, hal⟩ := ha
      obtain ⟨b, hPb, hbs, hbl⟩ := hb
      obtain ⟨hf1, _, _⟩ := closeOne_spec h1
      have hfr1 := hfr.trans hf1
      rcases List.sublist_cons_iff.1 hs with hs' | ⟨r, hr, hs'⟩
      · -- neither line is this step's
        have hir : i ∈ rest := hs'.subset (List.mem_cons_self ..)
        have hjr : j ∈ rest := hs'.subset (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have hic : i ≠ c := fun hc => hnd'.1 (hc ▸ hir)
        have hjc : j ≠ c := fun hc => hnd'.1 (hc ▸ hjr)
        obtain ⟨_, hcd1, a', ha', ha's, ha'l⟩ :=
          closeOne_keeps_untaken h1 hfr hcd hic hPa has hal hri hci
        obtain ⟨_, _, b', hb', hb's, hb'l⟩ :=
          closeOne_keeps_untaken h1 hfr hcd hjc hPb hbs hbl hrj hcj
        exact ih P1 Q h hnd'.2 hs' hfr1 hcd1 ⟨a', ha', ha's, ha'l⟩ ⟨b', hb', hb's, hb'l⟩ hdoc hlt
      · -- this step lands `i`
        injection hr with hci' hr
        subst hci'
        subst hr
        have hjr : j ∈ rest := List.singleton_sublist.1 hs'
        have hactP := closeAct_skel_frame (g := g) (now := now) hfr has
        obtain ⟨_, hcd1, b', hb', hb's, hb'l⟩ :=
          closeOne_keeps_untaken h1 hfr hcd (Ne.symm hij) hPb hbs hbl hrj hcj
        rcases closeOne_moves h1 with ⟨_, hst⟩ |
            ⟨e, k, spot, hPe, _, _, hds, ⟨f', hf', hlive⟩, hcar, hfil, hovr⟩ | ⟨_, hlives, e, r, hPe, hA, hx⟩
        · exact absurd (hactP.symm.trans (hst a hPa)) hne
        · rw [hPa] at hPe
          injection hPe with hPe
          subst hPe
          have hsrc : sectionAt P.val a.val.live = sectionAt p0.val ei.val.live := by
            rw [hal]; exact sectionAt_docs (hcd _ ri hri hci)
          refine fold_keeps_order_after_first g now fx p0 i j ej k hnej
            (fun hA => ?_) (fun r hA => ?_) (fun hA => ?_) (fun r hA => ?_) rest P1 Q h hnd'.2 hnd'.1 hjr
            hfr1 hcd1 ⟨b', hb', hb's, hb'l⟩ ⟨f', hf', by rw [hlive], fun r hA spot' hsp' n hn => ?_,
              fun hA spot' hsp' n hn => ?_⟩
          · rw [← carryTarget_frame hfr]; exact (hcar (hactP.trans (hact ▸ hA))).1
          · rw [← closeTarget_frame hfr]; exact (hfil r (hactP.trans (hact ▸ hA))).1
          · rw [← overdueTarget_frame hfr]; exact (hovr (hactP.trans (hact ▸ hA))).1
          · rw [hfold]; exact (hfil r (hactP.trans (hact ▸ hA))).2.2
          · have hAi : closeAct g now p0.val ei.val.skel = .file r := hact ▸ hA
            have hsp := (hfil r (hactP.trans hAi)).2.1
            rw [hsrc] at hsp
            have hsp2 : landingSpot P.val k (closePolicy g).landing (sectionAt p0.val ej.val.live) =
                .ok spot := by
              by_cases hl : (closePolicy g).landing = .sameSection
              · rw [← hsec (by rw [hAi]; simp) hl]; exact hsp
              · rw [landingSpot_src P.val k hl _ (sectionAt p0.val ei.val.live)]; exact hsp
            rw [hlive]
            exact landed_rank_lt_next_spot hds hsp2 spot' hsp' n hn
          · have hAi : closeAct g now p0.val ei.val.skel = .overdue := hact ▸ hA
            have hsp := (hovr (hactP.trans hAi)).2
            rw [hsrc] at hsp
            have hsp2 : landingSpot P.val k .overdueSection (sectionAt p0.val ej.val.live) =
                .ok spot := by
              rw [landingSpot_src P.val k (by decide) _ (sectionAt p0.val ei.val.live)]; exact hsp
            rw [hlive]
            exact landed_rank_lt_next_spot hds hsp2 spot' hsp' n hn
        · -- the fold drops `i`, so it drops `j` too, and both stay where they are
          rw [hPa] at hPe
          injection hPe with hPe
          subst hPe
          have hAj : closeAct g now p0.val ej.val.skel = .file r := by rw [hact, ← hactP]; exact hA
          have hxj : (fx j).isDrop = true := by rw [hfold]; exact hx
          have hli := hlives i
          rw [hPa] at hli
          obtain ⟨a', ha', hal'⟩ := get_of_map_eq_some hli
          simp only at hal'
          exact fold_keeps_order_of_drop g now fx p0 i j ej hAj hxj rest P1 Q h hnd'.2 hnd'.1 hjr hfr1 hcd1
            ⟨b', hb', hb's, hb'l⟩ ⟨a', ha', by rw [hal', hal, hdoc], by rw [hal', hal]; exact hlt⟩

theorem sublist_pair_or {i j : Id} (hij : i ≠ j) :
    ∀ l : List Id, i ∈ l → j ∈ l → [i, j].Sublist l ∨ [j, i].Sublist l := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons c t ih =>
    intro hi hj
    rcases List.mem_cons.1 hi with rfl | hi'
    · have hjt : j ∈ t := (List.mem_cons.1 hj).resolve_left (Ne.symm hij)
      exact Or.inl ((List.singleton_sublist.2 hjt).cons_cons _)
    · rcases List.mem_cons.1 hj with rfl | hj'
      · exact Or.inr ((List.singleton_sublist.2 hi').cons_cons _)
      · rcases ih hi' hj' with h | h
        · exact Or.inl (h.cons _)
        · exact Or.inr (h.cons _)

/-- **Gap 59's law: a close keeps source order.**  Two lines one close takes
from the same file, by the same action — both carried, both filed, or both moved to
the backlog's `# Overdue` (D7, re-proved per D5 over the fourth action) — land in
the same destination file in the order they had: the one above stays above.
When the row lands a line in the section it came from (§6.3's month row) the two
must have stood under the same heading, because the destination's sections are
ordered by the destination file, not the source (the one hypothesis that is not
about the fold).

Before `closeCands` sorted its candidates by (document, rank) this was false on
every loaded plan with two such lines: the loader builds `dom` in reverse, so the
fold took the lower line first and the higher one landed after it. -/
theorem close_keeps_source_order {g : Grain} {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close g now bm p = .ok q)
    {i j : Id} {ei ej : Entity} (hi : p.val.store.get i = some ei) (hj : p.val.store.get j = some ej)
    (htaken : closeAct g now p.val ei.val.skel ≠ .stay)
    (hact : closeAct g now p.val ej.val.skel = closeAct g now p.val ei.val.skel)
    (hfold : (foldFxOf g now bm p.val j).isDrop = (foldFxOf g now bm p.val i).isDrop)
    (hdoc : ei.val.live.doc = ej.val.live.doc)
    (hsec : closeAct g now p.val ei.val.skel ≠ .carry → (closePolicy g).landing = .sameSection →
      sectionAt p.val ei.val.live = sectionAt p.val ej.val.live)
    (hlt : ei.val.live.rank < ej.val.live.rank) :
    ∃ fi fj, q.val.store.get i = some fi ∧ q.val.store.get j = some fj ∧
      fi.val.live.doc = fj.val.live.doc ∧ fi.val.live.rank < fj.val.live.rank := by
  have hmi : i ∈ closeCands g now p.val := by
    by_cases hc : i ∈ closeCands g now p.val
    · exact hc
    · exact absurd (closeAct_of_not_mem_closeCands hc hi) htaken
  have hmj : j ∈ closeCands g now p.val := by
    by_cases hc : j ∈ closeCands g now p.val
    · exact hc
    · exact absurd (hact.symm.trans (closeAct_of_not_mem_closeCands hc hj)) htaken
  have hij : i ≠ j := by
    intro he; subst he; rw [hi] at hj; injection hj with hj; subst hj; exact Nat.lt_irrefl _ hlt
  have hsub : [i, j].Sublist (closeCands g now p.val) := by
    rcases sublist_pair_or hij _ hmi hmj with hs | hs
    · exact hs
    · exfalso
      have hle := List.pairwise_pair.1 ((closeCands_sorted g now p.val).sublist hs)
      have hsj : liveSiteOf p.val j = ej.val.live := by unfold liveSiteOf; rw [hj]
      have hsi : liveSiteOf p.val i = ei.val.live := by unfold liveSiteOf; rw [hi]
      rw [hsj, hsi, siteLe_iff] at hle
      rcases hle with hle | ⟨_, hle⟩
      · rw [hdoc] at hle; exact Nat.lt_irrefl _ hle
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hle)
  exact fold_keeps_order g now (foldFxOf g now bm p.val) p i j ei ej htaken hact hfold hsec
    (closeCands g now p.val) p q h
    (closeCands_nodup g now p.val) hsub (Frame.refl _) (fun _ _ _ _ => rfl)
    ⟨ei, hi, rfl, rfl⟩ ⟨ej, hj, rfl, rfl⟩ hdoc hlt

/-- **Both directions** (AGENTS §5.8): for two such lines at distinct ranks, the
one above in the source is the one above in the destination, and conversely. -/
theorem close_keeps_source_order_iff {g : Grain} {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close g now bm p = .ok q)
    {i j : Id} {ei ej fi fj : Entity} (hi : p.val.store.get i = some ei) (hj : p.val.store.get j = some ej)
    (hqi : q.val.store.get i = some fi) (hqj : q.val.store.get j = some fj)
    (htaken : closeAct g now p.val ei.val.skel ≠ .stay)
    (hact : closeAct g now p.val ej.val.skel = closeAct g now p.val ei.val.skel)
    (hfold : (foldFxOf g now bm p.val j).isDrop = (foldFxOf g now bm p.val i).isDrop)
    (hdoc : ei.val.live.doc = ej.val.live.doc)
    (hsec : closeAct g now p.val ei.val.skel ≠ .carry → (closePolicy g).landing = .sameSection →
      sectionAt p.val ei.val.live = sectionAt p.val ej.val.live)
    (hrank : ei.val.live.rank ≠ ej.val.live.rank) :
    ei.val.live.rank < ej.val.live.rank ↔ fi.val.live.rank < fj.val.live.rank := by
  constructor
  · intro hlt
    obtain ⟨fi', fj', hqi', hqj', _, hr⟩ := close_keeps_source_order h hi hj htaken hact hfold hdoc hsec hlt
    rw [hqi] at hqi'; injection hqi' with hqi'
    rw [hqj] at hqj'; injection hqj' with hqj'
    subst hqi' hqj'
    exact hr
  · intro hq
    rcases Nat.lt_or_gt_of_ne hrank with hlt | hgt
    · exact hlt
    · exfalso
      have htj : closeAct g now p.val ej.val.skel ≠ .stay := by rw [hact]; exact htaken
      obtain ⟨fj', fi', hqj', hqi', _, hr⟩ := close_keeps_source_order h hj hi htj hact.symm hfold.symm hdoc.symm
        (fun hc hl => (hsec (by rw [← hact]; exact hc) hl).symm) hgt
      rw [hqi] at hqi'; injection hqi' with hqi'
      rw [hqj] at hqj'; injection hqj' with hqj'
      subst hqi' hqj'
      exact Nat.lt_asymm hq hr


/-! ## Source order across the fold: the mixed pair (stage-4 final repair, defect 2)

`close_keeps_source_order` asks that the fold drop both lines or neither (`hfold`),
because a filed line and a child dropped with it end in different files — the law
without that clause is false (`a_dropped_child_and_its_filed_parent_part_ways`,
Boundary.lean).  The mixed pair still has an order law, stated over the sites the
two leave **in the file they were taken from**: the filed line's tombstone stands
exactly where the line stood (`close_leaves_a_copied_lines_tombstone_where_it_stood`),
and the dropped child stays exactly where it stood
(`close_leaves_a_dropped_line_where_it_stood`), so the one above stays above
(`close_keeps_source_order_across_the_fold`).  With it every pair of lines one close
takes from one file by one action has an order law: both dropped or both not by
`close_keeps_source_order`, one of each by this section.  Neither half moves a site:
no step of a close shifts a closed file (`closeOne_get_others`: a landing's shift is
in an open one). -/

/-- An entity after a landing's shift in document `k` (`none`: no shift). -/
def Entity.bumpIn (k : DocIx) : Option Nat → Entity → Entity
  | none,   e => e
  | some n, e => e.shiftIn k n

theorem Entity.bumpIn_live {k : DocIx} (spot : Option Nat) {e : Entity} (hk : e.val.live.doc ≠ k) :
    (e.bumpIn k spot).val.live = e.val.live := by
  cases spot with
  | none => rfl
  | some n =>
    show e.val.live.shiftIn k n = e.val.live
    unfold Site.shiftIn
    rw [if_neg hk]

theorem Entity.bumpIn_archiveSite {k : DocIx} (spot : Option Nat) {e : Entity} {s : Site}
    (hs : e.val.archiveSite = some s) (hk : s.doc ≠ k) :
    (e.bumpIn k spot).val.archiveSite = some s := by
  cases spot with
  | none => exact hs
  | some n =>
    show (e.val.archive.map (fun t => { t with site := t.site.shiftIn k n })).map Tomb.site = some s
    unfold Core.archiveSite at hs
    cases ha : e.val.archive with
    | none => rw [ha] at hs; cases hs
    | some t =>
      rw [ha] at hs
      simp only [Option.map_some, Option.some.injEq] at hs ⊢
      subst hs
      unfold Site.shiftIn
      rw [if_neg hk]

/-- **What a landing does to every entity**: the landed id is `f` of it, shifted;
every other is shifted, and nothing else. -/
theorem landAt_get {p q : WfPlan} {k : DocIx} {spot : Option Nat} {i : Id}
    {f : Site → Entity → Except KErr Entity} (h : landAt p k spot i f = .ok q) :
    (∀ j, j ≠ i → q.val.store.get j = (p.val.store.get j).map (Entity.bumpIn k spot)) ∧
      ∃ e f', p.val.store.get i = some e ∧
        f ⟨k, spot.getD (endRank p.val k)⟩ (e.bumpIn k spot) = .ok f' ∧ q.val.store.get i = some f' := by
  cases spot with
  | none =>
    unfold landAt at h
    obtain ⟨_, hj, e, e', hget, hf, hq⟩ := WfPlan.mapAt_spec h
    refine ⟨fun j hji => ?_, e, e', hget, hf, hq⟩
    rw [hj j hji]
    cases p.val.store.get j <;> rfl
  | some n =>
    unfold landAt at h
    simp only at h
    cases h1 : p.shiftAt k n with
    | error x => simp [h1] at h
    | ok q1 =>
      simp only [h1] at h
      have hv := WfPlan.shiftAt_val h1
      obtain ⟨_, hj, e1, e', hget1, hf, hq⟩ := WfPlan.mapAt_spec h
      have hg : ∀ j, q1.val.store.get j = (p.val.store.get j).map (Entity.shiftIn k n) := by
        intro j
        rw [hv]
        rfl
      refine ⟨fun j hji => ?_, ?_⟩
      · rw [hj j hji, hg j]
        cases p.val.store.get j <;> rfl
      · rw [hg i] at hget1
        obtain ⟨e, he, hee⟩ := Option.map_eq_some_iff.1 hget1
        subst hee
        exact ⟨e, e', he, hf, hq⟩

/-- **One step, seen from every id it does not take**: at most one shift, and only in
a file that is not closed. -/
theorem closeOne_get_others {g : Grain} {now : Day} {x : FoldFx} {i : Id} {p q : WfPlan}
    (h : closeOne g now x i p = .ok q) :
    ∃ k spot, (∀ n, spot = some n → docOpenAt now p.val k) ∧
      ∀ j, j ≠ i → q.val.store.get j = (p.val.store.get j).map (Entity.bumpIn k spot) := by
  have hid : ∀ j, (p.val.store.get j).map (Entity.bumpIn 0 none) = p.val.store.get j := by
    intro j
    cases p.val.store.get j <;> rfl
  unfold closeOne at h
  split at h
  · simp at h
  · split at h
    · injection h with h
      subst h
      exact ⟨0, none, (fun _ hn => nomatch hn), fun j _ => (hid j).symm⟩
    · split at h
      · simp at h
      · rename_i k _
        exact ⟨k, none, (fun _ hn => nomatch hn), (landAt_get h).1⟩
    · split at h
      · obtain ⟨_, hj, _⟩ := WfPlan.mapAt_spec h
        exact ⟨0, none, (fun _ hn => nomatch hn), fun j hji => by rw [hj j hji, hid j]⟩
      · split at h
        · simp at h
        · rename_i k hk
          split at h
          · simp at h
          · rename_i spot _
            refine ⟨k, spot, fun _ _ => ?_, (landAt_get (guardStray_ok h).1).1⟩
            obtain ⟨_, _, hreg⟩ := findDocIx_spec hk
            intro r hr
            rw [hreg] at hr
            injection hr with hr
            subst hr
            exact closeTo_target_is_open g now
    · split at h
      · simp at h
      · rename_i k hk
        split at h
        · simp at h
        · rename_i spot _
          refine ⟨k, spot, fun _ _ => ?_, (landAt_get h).1⟩
          obtain ⟨_, _, hreg⟩ := overdueTarget_spec hk
          intro r hr
          rw [hreg] at hr
          cases hr

/-- **The fold moves no site of a closed file**, for an id it does not take — a
live line or a tombstone, whichever `obs` reads. -/
theorem fold_keeps_a_closed_site (g : Grain) (now : Day) (fx : Id → FoldFx) (p0 : WfPlan) (x : Id)
    (obs : Entity → Option Site)
    (hobs : ∀ (k : DocIx) (spot : Option Nat) (e : Entity) (s : Site), obs e = some s → s.doc ≠ k →
      obs (e.bumpIn k spot) = some s)
    {s : Site} {r : Region} (hr : docRegion p0.val s.doc = some r) (hc : Closed r now) :
    ∀ (l : List Id) (P Q : WfPlan), l.foldlM (fun q c => closeOne g now (fx c) c q) P = .ok Q →
      x ∉ l → Frame p0.val P.val → (∃ b, P.val.store.get x = some b ∧ obs b = some s) →
      ∃ b, Q.val.store.get x = some b ∧ obs b = some s := by
  intro l
  induction l with
  | nil =>
    intro P Q h _ _ hb
    simp only [List.foldlM_nil] at h
    injection h with h
    subst h
    exact hb
  | cons c rest ih =>
    intro P Q h hx hfr hb
    simp only [List.foldlM_cons] at h
    cases h1 : closeOne g now (fx c) c P with
    | error e => rw [h1] at h; simp [bind, Except.bind] at h
    | ok P1 =>
      rw [h1] at h
      simp only [bind, Except.bind] at h
      have hxc : x ≠ c := fun he => hx (he ▸ List.mem_cons_self ..)
      obtain ⟨hf1, _, _⟩ := closeOne_spec h1
      obtain ⟨k, spot, hopen, hget⟩ := closeOne_get_others h1
      obtain ⟨b, hPb, hbs⟩ := hb
      refine ih P1 Q h (fun hm => hx (List.mem_cons_of_mem _ hm)) (hfr.trans hf1) ⟨b.bumpIn k spot, ?_, ?_⟩
      · rw [hget x hxc, hPb]
        rfl
      · cases hsp : spot with
        | none => exact hbs
        | some n =>
          refine hobs k (some n) b s hbs (fun hsk => ?_)
          exact hopen n hsp r (by rw [← hsk, hfr.2.2]; exact hr) hc

/-- **The fold, for a line it drops**: the line ends where it stood. -/
theorem fold_keeps_a_dropped_line_in_place (g : Grain) (now : Day) (fx : Id → FoldFx) (p0 : WfPlan)
    (j : Id) (ej : Entity) {r0 : Region} (hactj : closeAct g now p0.val ej.val.skel = .file r0)
    (hxj : (fx j).isDrop = true) :
    ∀ (l : List Id) (P Q : WfPlan), l.foldlM (fun q c => closeOne g now (fx c) c q) P = .ok Q →
      l.Nodup → j ∈ l → Frame p0.val P.val → ClosedDocsKept now p0.val P.val →
      (∃ b, P.val.store.get j = some b ∧ b.val.skel = ej.val.skel ∧ b.val.live = ej.val.live) →
      ∃ b, Q.val.store.get j = some b ∧ b.val.live = ej.val.live := by
  obtain ⟨r1, hr1, hc1⟩ :=
    closeAct_closed (show closeAct g now p0.val ej.val.skel ≠ .stay by rw [hactj]; simp)
  intro l
  induction l with
  | nil => intro _ _ _ _ hj; simp at hj
  | cons c rest ih =>
    intro P Q h hnd hj hfr hcd hb
    simp only [List.foldlM_cons] at h
    cases h1 : closeOne g now (fx c) c P with
    | error x => rw [h1] at h; simp [bind, Except.bind] at h
    | ok P1 =>
      rw [h1] at h
      simp only [bind, Except.bind] at h
      have hnd' := List.nodup_cons.1 hnd
      obtain ⟨b, hPb, hbs, hbl⟩ := hb
      obtain ⟨hf1, _, _⟩ := closeOne_spec h1
      have hfr1 := hfr.trans hf1
      by_cases hjc : j = c
      · subst hjc
        have hactP := closeAct_skel_frame (g := g) (now := now) hfr hbs
        rcases closeOne_moves h1 with ⟨_, hst⟩ | ⟨_, _, _, hPe, _, _, _, _, _, hfil, _⟩ |
            ⟨_, hlives, _⟩
        · exact absurd (hactP.symm.trans (hst b hPb)) (by rw [hactj]; simp)
        · rw [hPb] at hPe
          injection hPe with hPe
          subst hPe
          have := (hfil r0 (hactP.trans hactj)).2.2
          rw [hxj] at this
          cases this
        · have hlj := hlives j
          rw [hPb] at hlj
          obtain ⟨b', hb', hbl'⟩ := get_of_map_eq_some hlj
          simp only at hbl'
          obtain ⟨b'', hb'', hl''⟩ := fold_keeps_a_closed_site g now fx p0 j (fun e => some e.val.live)
            (fun k spot e s hs hk => by
              simp only [Option.some.injEq] at hs ⊢
              subst hs
              exact Entity.bumpIn_live spot hk)
            (s := ej.val.live) hr1 hc1 rest P1 Q h hnd'.1 hfr1 ⟨b', hb', by rw [hbl', hbl]⟩
          exact ⟨b'', hb'', Option.some.inj hl''⟩
      · have hjr : j ∈ rest := (List.mem_cons.1 hj).resolve_left hjc
        obtain ⟨_, hcd1, b', hb', hb's, hb'l⟩ :=
          closeOne_keeps_untaken h1 hfr hcd hjc hPb hbs hbl hr1 hc1
        exact ih P1 Q h hnd'.2 hjr hfr1 hcd1 ⟨b', hb', hb's, hb'l⟩

/-- **The fold, for a line it copies forward**: its tombstone stands where the line
stood. -/
theorem fold_leaves_a_copied_lines_tombstone_where_it_stood (g : Grain) (now : Day)
    (fx : Id → FoldFx) (p0 : WfPlan) (i : Id) (ei : Entity) {r0 : Region}
    (hacti : closeAct g now p0.val ei.val.skel = .file r0) (hxi : (fx i).isDrop = false)
    (hcopy : (closePolicy g).disposition = .copy) :
    ∀ (l : List Id) (P Q : WfPlan), l.foldlM (fun q c => closeOne g now (fx c) c q) P = .ok Q →
      l.Nodup → i ∈ l → Frame p0.val P.val → ClosedDocsKept now p0.val P.val →
      (∃ b, P.val.store.get i = some b ∧ b.val.skel = ei.val.skel ∧ b.val.live = ei.val.live) →
      ∃ b, Q.val.store.get i = some b ∧ b.val.archiveSite = some ei.val.live := by
  obtain ⟨r1, hr1, hc1⟩ :=
    closeAct_closed (show closeAct g now p0.val ei.val.skel ≠ .stay by rw [hacti]; simp)
  intro l
  induction l with
  | nil => intro _ _ _ _ hi; simp at hi
  | cons c rest ih =>
    intro P Q h hnd hi hfr hcd hb
    simp only [List.foldlM_cons] at h
    cases h1 : closeOne g now (fx c) c P with
    | error x => rw [h1] at h; simp [bind, Except.bind] at h
    | ok P1 =>
      rw [h1] at h
      simp only [bind, Except.bind] at h
      have hnd' := List.nodup_cons.1 hnd
      obtain ⟨b, hPb, hbs, hbl⟩ := hb
      obtain ⟨hf1, _, _⟩ := closeOne_spec h1
      have hfr1 := hfr.trans hf1
      by_cases hic : i = c
      · subst hic
        have hactP := closeAct_skel_frame (g := g) (now := now) hfr hbs
        have hr1' : docRegion p0.val ei.val.live.doc = some r1 := hr1
        have hne : ∀ k, docRegion P.val k = some (closeTo g now) → b.val.live.doc ≠ k := by
          intro k hk hbk
          rw [← hbk, hbl, hfr.2.2, hr1'] at hk
          injection hk with hk
          subst hk
          exact closeTo_target_is_open g now hc1
        have hstep : ∃ f', P1.val.store.get i = some f' ∧ f'.val.archiveSite = some ei.val.live := by
          unfold closeOne at h1
          split at h1
          · simp at h1
          · rename_i e hget
            rw [hPb] at hget
            injection hget with hget
            subst hget
            split at h1
            · rename_i hst
              exact absurd (hactP.symm.trans hst) (by rw [hacti]; simp)
            · rename_i hst
              exact absurd (hactP.symm.trans hst) (by rw [hacti]; simp)
            · rename_i r hact
              have hrr : r0 = r := by
                have := hactP.symm.trans hact
                rw [hacti] at this
                injection this
              subst hrr
              split at h1
              · rename_i hx
                rw [hxi] at hx
                cases hx
              · split at h1
                · simp at h1
                · rename_i k hk
                  split at h1
                  · simp at h1
                  · rename_i spot _
                    obtain ⟨_, e0, f', hget0, hfe, hq⟩ := landAt_get (guardStray_ok h1).1
                    rw [hPb] at hget0
                    injection hget0 with hget0
                    subst hget0
                    obtain ⟨_, _, hreg⟩ := findDocIx_spec hk
                    have hlive := Entity.bumpIn_live spot (hne k hreg)
                    unfold fileE at hfe
                    rw [hcopy] at hfe
                    simp only at hfe
                    split at hfe
                    · rename_i st _
                      have hv := refileX_roundtrips _ _ _ _ _ hfe
                      refine ⟨f', hq, ?_⟩
                      unfold Core.archiveSite
                      rw [hv]
                      simp only [Option.map_some]
                      rw [hlive, hbl]
                    · simp at hfe
            · rename_i hst
              exact absurd (hactP.symm.trans hst) (by rw [hacti]; simp)
        obtain ⟨f', hq, hsite⟩ := hstep
        exact fold_keeps_a_closed_site g now fx p0 i (fun e => e.val.archiveSite)
          (fun k spot e s hs hk => Entity.bumpIn_archiveSite spot hs hk)
          (s := ei.val.live) hr1 hc1 rest P1 Q h hnd'.1 hfr1 ⟨f', hq, hsite⟩
      · have hir : i ∈ rest := (List.mem_cons.1 hi).resolve_left hic
        obtain ⟨_, hcd1, b', hb', hb's, hb'l⟩ :=
          closeOne_keeps_untaken h1 hfr hcd hic hPb hbs hbl hr1 hc1
        exact ih P1 Q h hnd'.2 hir hfr1 hcd1 ⟨b', hb', hb's, hb'l⟩

theorem mem_closeCands_of_ne_stay {g : Grain} {now : Day} {p : PlanCore} {i : Id} {e : Entity}
    (hi : p.store.get i = some e) (h : closeAct g now p e.val.skel ≠ .stay) : i ∈ closeCands g now p := by
  by_cases hc : i ∈ closeCands g now p
  · exact hc
  · exact absurd (closeAct_of_not_mem_closeCands hc hi) h

/-- A line the week close drops is one it files (`dropsInto_spec`), at the week row. -/
theorem files_of_isDrop {g : Grain} {now : Day} {bm : Nat} {p : PlanCore} {j : Id} {ej : Entity}
    (hj : p.store.get j = some ej) (hxj : (foldFxOf g now bm p j).isDrop = true) :
    g = week ∧ ∃ r, closeAct g now p ej.val.skel = .file r := by
  rw [foldFxOf_isDrop] at hxj
  obtain ⟨r, hd⟩ := Option.isSome_iff_exists.1 hxj
  obtain ⟨hg, _, _, ej', _, hj', _, hfj, _, _⟩ := dropsInto_spec hd
  rw [hj] at hj'
  injection hj' with hj'
  rw [← hj'] at hfj
  exact ⟨hg, filesLine_iff.1 hfj⟩

/-- **A child the week close drops ends where it stood** — its file and its rank. -/
theorem close_leaves_a_dropped_line_where_it_stood {g : Grain} {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close g now bm p = .ok q) {j : Id} {ej : Entity} (hj : p.val.store.get j = some ej)
    (hxj : (foldFxOf g now bm p.val j).isDrop = true) :
    ∃ fj, q.val.store.get j = some fj ∧ fj.val.live = ej.val.live := by
  obtain ⟨_, r0, hact⟩ := files_of_isDrop hj hxj
  exact fold_keeps_a_dropped_line_in_place g now (foldFxOf g now bm p.val) p j ej hact hxj
    (closeCands g now p.val) p q h (closeCands_nodup g now p.val)
    (mem_closeCands_of_ne_stay hj (by rw [hact]; simp)) (Frame.refl _) (fun _ _ _ _ => rfl)
    ⟨ej, hj, rfl, rfl⟩

/-- **A line a copying row files forward leaves its tombstone where it stood** — its
file and its rank, whatever else the close lands or shifts. -/
theorem close_leaves_a_copied_lines_tombstone_where_it_stood {g : Grain} {now : Day} {bm : Nat}
    {p q : WfPlan} (h : close g now bm p = .ok q) {i : Id} {ei : Entity} {r : Region}
    (hi : p.val.store.get i = some ei) (hact : closeAct g now p.val ei.val.skel = .file r)
    (hxi : (foldFxOf g now bm p.val i).isDrop = false) (hcopy : (closePolicy g).disposition = .copy) :
    ∃ fi, q.val.store.get i = some fi ∧ fi.val.archiveSite = some ei.val.live :=
  fold_leaves_a_copied_lines_tombstone_where_it_stood g now (foldFxOf g now bm p.val) p i ei hact hxi hcopy
    (closeCands g now p.val) p q h (closeCands_nodup g now p.val)
    (mem_closeCands_of_ne_stay hi (by rw [hact]; simp)) (Frame.refl _) (fun _ _ _ _ => rfl)
    ⟨ei, hi, rfl, rfl⟩

/-- **The mixed pair keeps source order** (the case `close_keeps_source_order`'s `hfold`
leaves out).  Two lines one close takes from one file by one action, the fold dropping
`j` and not `i`: `i`'s tombstone and `j` stand in that file in the order `i` and `j`
had — the one above stays above, in both directions. -/
theorem close_keeps_source_order_across_the_fold {g : Grain} {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close g now bm p = .ok q)
    {i j : Id} {ei ej : Entity} (hi : p.val.store.get i = some ei) (hj : p.val.store.get j = some ej)
    (hact : closeAct g now p.val ej.val.skel = closeAct g now p.val ei.val.skel)
    (hxi : (foldFxOf g now bm p.val i).isDrop = false)
    (hxj : (foldFxOf g now bm p.val j).isDrop = true)
    (hdoc : ei.val.live.doc = ej.val.live.doc) :
    ∃ fi fj t, q.val.store.get i = some fi ∧ q.val.store.get j = some fj ∧
      fi.val.archiveSite = some t ∧ t.doc = fj.val.live.doc ∧
      (ei.val.live.rank < ej.val.live.rank ↔ t.rank < fj.val.live.rank) := by
  obtain ⟨hg, r0, hactj⟩ := files_of_isDrop hj hxj
  subst hg
  obtain ⟨fi, hfi, hti⟩ :=
    close_leaves_a_copied_lines_tombstone_where_it_stood h hi (hact.symm.trans hactj) hxi rfl
  obtain ⟨fj, hfj, hlj⟩ := close_leaves_a_dropped_line_where_it_stood h hj hxj
  exact ⟨fi, fj, ei.val.live, hfi, hfj, hti, by rw [hlj, hdoc], by rw [hlj]⟩

/-! ## Gap 55 closed: dated work routes itself (the owner's D7 and D8)

Until the owner's decisions of 2026-09-13 a week line with `due:` was filed like any
other, its `# Demoted` record broke the month rule "an outcome carries no date", and
the whole week close refused `badHorizon` — §4.3's own example week, a week after
`tm init --example`, refused its automatic close on every command (README gap 55).
Now the week row routes the line by its date (`closeAct`'s fourth action):

* **past due, `persist`** (D7): moved to the end of `backlog.md`'s `# Overdue`, box,
  bytes and tombstone as they were — no stamp, no `[-]` left behind
  (`close_moves_a_past_due_persist_line_to_the_backlog`);
* **anything else dated** — not yet due, or past due with `on-miss:expire`/`next`
  (D8): filed like any unfinished line, `[-]` left behind and a stamped record in
  `# Demoted`, which keeps the line's date
  (`close_week_files_a_dated_line_it_does_not_drop_keeping_its_date`),
  and `shapesWf` admits that record since D8 (`demotedRecordPlacement`, Plan.lean).

The two-run laws this re-proves in place (D5): `close_is_idempotent` (L16) — a backlog
has no region, so nothing D7 moves is ever taken again (`closeAct_of_regionless`);
`close_keeps_source_order` — two overdue lines of one week land in `# Overdue` in the
order they had (`fold_keeps_order` over the fourth action); the L19 theorems, whose
argument is `stepSkel_lands_outside_every_closed_region`; and, in Report.lean, the
report agreement over the sixth disposition, `moveOverdue`. -/

namespace Field

theorem lookup_filterMap_cons_congr (k : Key) (t : Tok) {xs ys : List Tok}
    (h : List.lookup k (xs.filterMap (fun x => rawKeyPair x.word)) =
      List.lookup k (ys.filterMap (fun x => rawKeyPair x.word))) :
    List.lookup k ((t :: xs).filterMap (fun x => rawKeyPair x.word)) =
      List.lookup k ((t :: ys).filterMap (fun x => rawKeyPair x.word)) := by
  cases hr : rawKeyPair t.word with
  | none => rw [filterMap_cons_none' _ t xs hr, filterMap_cons_none' _ t ys hr]; exact h
  | some p =>
    rw [filterMap_cons_some' _ t p xs hr, filterMap_cons_some' _ t p ys hr]
    obtain ⟨a, b⟩ := p
    by_cases hk : k = a
    · subst hk
      rw [lookup_cons_self, lookup_cons_self]
    · rw [lookup_cons_ne k a b _ hk, lookup_cons_ne k a b _ hk]; exact h

theorem isKeyTok_of_keyOf_ne {k' : Key} {t : Tok} (h : keyOf t.word ≠ some k') : isKeyTok k' t = false := by
  unfold isKeyTok
  exact beq_false_of_ne h

theorem lookup_setKeyIn_other {k k' : Key} (hne : k' ≠ k) (v : List Char) : ∀ ts : List Tok,
    List.lookup k' ((setKeyIn k v ts).filterMap (fun x => rawKeyPair x.word)) =
      List.lookup k' (ts.filterMap (fun x => rawKeyPair x.word))
  | [] => rfl
  | t :: ts => by
    by_cases hk : isKeyTok k t = true
    · have h1 : isKeyTok k' ⟨t.sep, keyWord k v⟩ = false :=
        isKeyTok_of_keyOf_ne (by rw [keyOf_keyWord]; exact fun hc => hne (Option.some.inj hc).symm)
      have h2 : isKeyTok k' t = false := by
        apply isKeyTok_of_keyOf_ne
        unfold isKeyTok at hk
        rw [beq_iff_eq.1 hk]
        exact fun hc => hne (Option.some.inj hc).symm
      rw [setKeyIn_cons_pos k v t ts hk, lookup_cons_skip k' _ _ h1, lookup_cons_skip k' _ _ h2]
    · simp only [Bool.not_eq_true] at hk
      rw [setKeyIn_cons_neg k v t ts hk]
      exact lookup_filterMap_cons_congr k' t (lookup_setKeyIn_other hne v ts)

theorem lookup_insertBeforeId_other {k' : Key} {w : List Char} (hw : keyOf w ≠ some k') :
    ∀ ts : List Tok,
      List.lookup k' ((insertBeforeId w ts).filterMap (fun x => rawKeyPair x.word)) =
        List.lookup k' (ts.filterMap (fun x => rawKeyPair x.word))
  | [] => by
    rw [insertBeforeId_nil, lookup_cons_skip k' _ _ (isKeyTok_of_keyOf_ne hw)]
  | u :: us => by
    by_cases hid : isIdWord u.word = true
    · by_cases hs : u.sep.isEmpty = true
      · rw [insertBeforeId_id_nosep w u us hid hs, lookup_cons_skip k' _ _ (isKeyTok_of_keyOf_ne hw)]
        rfl
      · simp only [Bool.not_eq_true] at hs
        rw [insertBeforeId_id_sep w u us hid hs, lookup_cons_skip k' _ _ (isKeyTok_of_keyOf_ne hw)]
    · simp only [Bool.not_eq_true] at hid
      rw [insertBeforeId_other w u us hid]
      exact lookup_filterMap_cons_congr k' u (lookup_insertBeforeId_other hw us)

/-- **Setting one key leaves every other key's reading alone.** -/
theorem lookupKey_setKey_other {k k' : Key} (hne : k' ≠ k) (v : List Char) (r : RawItem) :
    lookupKey k' (setKey k v r) = lookupKey k' r := by
  unfold lookupKey
  rw [keyPairs_raw, keyPairs_raw]
  unfold setKey
  split
  · exact lookup_setKeyIn_other hne v r.toks
  · exact lookup_insertBeforeId_other
      (by rw [keyOf_keyWord]; exact fun hc => hne (Option.some.inj hc).symm) r.toks

theorem isEstKey_keyOf {w : List Char} (h : isEstKey w = true) : keyOf w = some .est := by
  unfold isEstKey at h
  match w, h with
  | a :: b :: c :: d :: rest, h =>
    simp only [List.take, beq_iff_eq, List.cons.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, _⟩ := h
    rfl
  | [], h => simp at h
  | [_], h => simp at h
  | [_, _], h => simp at h
  | [_, _, _], h => simp at h

theorem lookup_setEstInTo_other {k' : Key} (hk : k' ≠ .est) (v : List Char) : ∀ ts : List Tok,
    List.lookup k' ((setEstInTo (['e', 's', 't', ':'] ++ v) ts).filterMap (fun x => rawKeyPair x.word)) =
      List.lookup k' (ts.filterMap (fun x => rawKeyPair x.word))
  | [] => rfl
  | t :: ts => by
    by_cases he : isEstKey t.word = true
    · have hw : isEstKey (['e', 's', 't', ':'] ++ v) = true := by simp [isEstKey]
      have h1 : isKeyTok k' ⟨t.sep, ['e', 's', 't', ':'] ++ v⟩ = false :=
        isKeyTok_of_keyOf_ne (by rw [isEstKey_keyOf hw]; exact fun hc => hk (Option.some.inj hc).symm)
      have h2 : isKeyTok k' t = false :=
        isKeyTok_of_keyOf_ne (by rw [isEstKey_keyOf he]; exact fun hc => hk (Option.some.inj hc).symm)
      show List.lookup k' ((if isEstKey t.word then (⟨t.sep, ['e', 's', 't', ':'] ++ v⟩ : Tok) :: ts
          else t :: setEstInTo (['e', 's', 't', ':'] ++ v) ts).filterMap (fun x => rawKeyPair x.word)) = _
      rw [if_pos he, lookup_cons_skip k' _ _ h1, lookup_cons_skip k' _ _ h2]
    · show List.lookup k' ((if isEstKey t.word then (⟨t.sep, ['e', 's', 't', ':'] ++ v⟩ : Tok) :: ts
          else t :: setEstInTo (['e', 's', 't', ':'] ++ v) ts).filterMap (fun x => rawKeyPair x.word)) = _
      rw [if_neg he]
      exact lookup_filterMap_cons_congr k' t (lookup_setEstInTo_other hk v ts)

/-- **The fold's `est:` setter leaves every other key's reading alone.** -/
theorem lookupKey_setEstTo_other {k' : Key} (hk : k' ≠ .est) (v : List Char) (r : RawItem) :
    lookupKey k' (setEstTo v r) = lookupKey k' r := by
  unfold lookupKey
  rw [keyPairs_raw, keyPairs_raw]
  unfold setEstTo
  split
  · exact lookup_setEstInTo_other hk v r.toks
  · have hw : isEstKey (['e', 's', 't', ':'] ++ v) = true := by simp [isEstKey]
    exact lookup_insertBeforeId_other
      (by rw [isEstKey_keyOf hw]; exact fun hc => hk (Option.some.inj hc).symm) r.toks

/-- `viewShape` reads four keys, none of which a close writes. -/
theorem viewShape_congr {r r' : RawItem}
    (h : ∀ k : Key, k ≠ .demoted → k ≠ .est → lookupKey k r = lookupKey k r') :
    viewShape r = viewShape r' := by
  unfold viewShape viewAt viewWin viewDur viewDue
  rw [h .interval (by decide) (by decide), h .window (by decide) (by decide),
    h .dur (by decide) (by decide), h .due (by decide) (by decide)]

end Field

/-- Carrying a record's estimate onto a line writes an `est:` token and nothing
else a key reads. -/
theorem lookupKey_carryEst_other {k' : Field.Key} (hk : k' ≠ .est) (t line : RawItem) :
    Field.lookupKey k' (carryEst t line) = Field.lookupKey k' line := by
  unfold carryEst
  split
  · rfl
  · split
    · rename_i tok htok
      unfold Field.lookupKey
      rw [Field.keyPairs_raw, Field.keyPairs_raw]
      have hw : isEstKey tok.word = true := by
        have := List.find?_some htok
        simpa using this
      exact Field.lookup_insertBeforeId_other
        (by rw [Field.isEstKey_keyOf hw]; exact fun hc => hk (Option.some.inj hc).symm) line.toks
    · rfl

/-- **A filed record keeps the line's date.**  The week row's record is the line
with `demoted:` set over the carried estimate; neither token is one `viewShape`
reads, so the `due:` (or `at:`, or `win:`) it had is the one it has. -/
theorem viewShape_refiledLine (st : Stamp) (a : Option RawItem) (l : RawItem) :
    Field.viewShape (refiledLine st a l) = Field.viewShape l := by
  cases a with
  | none =>
    exact Field.viewShape_congr (fun k hd _ => Field.lookupKey_setKey_other hd _ _)
  | some t =>
    exact Field.viewShape_congr (fun k hd he =>
      (Field.lookupKey_setKey_other hd _ _).trans (lookupKey_carryEst_other he t l))

theorem lookupKey_apply_other {k' : Field.Key} (hk : k' ≠ .est) (x : FoldFx) (l : RawItem) :
    Field.lookupKey k' (x.apply l) = Field.lookupKey k' l := by
  cases x with
  | none => rfl
  | drop => rfl
  | lift bm n =>
    show Field.lookupKey k' (foldEst bm n l) = _
    unfold foldEst
    split
    · rfl
    · exact Field.lookupKey_setEstTo_other hk _ l

/-- **A filed record keeps the line's date, under the fold too.** -/
theorem viewShape_refiledLineX (x : FoldFx) (st : Stamp) (a : Option RawItem) (l : RawItem) :
    Field.viewShape (refiledLineX x st a l) = Field.viewShape l := by
  cases a with
  | none =>
    exact Field.viewShape_congr (fun k hd he =>
      (Field.lookupKey_setKey_other hd _ _).trans (lookupKey_apply_other he x l))
  | some t =>
    exact Field.viewShape_congr (fun k hd he =>
      (Field.lookupKey_setKey_other hd _ _).trans
        ((lookupKey_apply_other he x _).trans (lookupKey_carryEst_other he t l)))

theorem refiledLineX_stamps_mem (x : FoldFx) (st : Stamp) (a : Option RawItem) (l : RawItem) :
    st ∈ (Field.viewDemoted (refiledLineX x st a l)).getD [] := by
  cases a with
  | none =>
    show st ∈ (Field.viewDemoted (Field.setDemoted (stampsOfLine l ++ [st]) _)).getD []
    rw [Field.view_set_demoted _ _ (by simp)]
    simp
  | some t =>
    show st ∈ (Field.viewDemoted (Field.setDemoted (mergeStamps (stampsOfLine t) (stampsOfLine l) st)
      _)).getD []
    have hm := ((mergeStamps_spec (stampsOfLine t) (stampsOfLine l) st).2 st).2 (Or.inr (Or.inr rfl))
    rw [Field.view_set_demoted _ _ (List.ne_nil_of_mem hm)]
    exact hm

/-- A filed record carries the stamp its close appends — over a line with no
standing record, and merged into one that has it (`mergeStamps_spec`). -/
theorem refiledLine_stamps_mem (st : Stamp) (a : Option RawItem) (l : RawItem) :
    st ∈ (Field.viewDemoted (refiledLine st a l)).getD [] := by
  cases a with
  | none =>
    show st ∈ (Field.viewDemoted (Field.setDemoted (stampsOfLine l ++ [st]) l)).getD []
    rw [Field.view_set_demoted _ _ (by simp)]
    simp
  | some t =>
    show st ∈ (Field.viewDemoted (Field.setDemoted (mergeStamps (stampsOfLine t) (stampsOfLine l) st)
      (carryEst t l))).getD []
    have hm := ((mergeStamps_spec (stampsOfLine t) (stampsOfLine l) st).2 st).2 (Or.inr (Or.inr rfl))
    rw [Field.view_set_demoted _ _ (List.ne_nil_of_mem hm)]
    exact hm

/-- **Past due with `persist`, in the core's own terms**: §5.3's effective
`on_miss` is `persist`, and the line is a point due on a day before `now`'s or an
interval that ended on one. -/
theorem Core.skel_overdue_iff (c : Core) (now : Day) :
    c.skel.overdue now = true ↔ effectiveOnMiss c = .persist ∧
      ((∃ m, c.shape = Shape.point m ∧ m.day < now) ∨
        (∃ a b, c.shape = Shape.interval a b ∧ b.day < now)) := by
  show (match (match Field.viewShape c.line with
          | .point m => some m.day | .interval _ b => some b.day | _ => none) with
        | some d => decide (d < now) && decide (c.skel.onMiss = .persist)
        | none => false) = true ↔ _
  rw [Core.skel_onMiss]
  have hs : c.shape = Field.viewShape c.line := rfl
  rw [hs]
  cases Field.viewShape c.line with
  | none => simp
  | point m =>
    simp only [Shape.point.injEq, exists_eq_left', decide_eq_true_eq, Bool.and_eq_true]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Or.inl h1⟩,
      fun ⟨h2, h1⟩ => ⟨by simpa using h1, h2⟩⟩
  | interval a b =>
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · exact fun ⟨h1, h2⟩ => ⟨h2, Or.inr ⟨a, b, rfl, h1⟩⟩
    · rintro ⟨h2, ⟨m, hm, _⟩ | ⟨a', b', hab, h1⟩⟩
      · cases hm
      · injection hab with _ hb
        subst hb
        exact ⟨h1, h2⟩
  | window r d => simp

/-! ### Under `# Overdue`: where D7's route lands a line, it stays -/

/-- No grain closes into a backlog: a close files into a week or a month file, and
carries into a week. -/
theorem kindOfGrain_is_never_backlog : ∀ g : Grain, kindOfGrain g ≠ .backlog := by
  decide

theorem pairwise_of_ranksAscend : ∀ (l : List (Nat × List Char)),
    ranksAscend l = true → l.Pairwise (fun a b => a.1 < b.1)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
    simp only [ranksAscend, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_ranksAscend (b :: t) h.2
    refine List.pairwise_cons.2 ⟨fun x hx => ?_, ih⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (List.pairwise_cons.1 ih |>.1 x hx)

/-- Two prose lines of one document at one rank are one line. -/
theorem prose_eq_of_rank {l : List (Nat × List Char)} (h : ranksAscend l = true)
    {a b : Nat × List Char} (ha : a ∈ l) (hb : b ∈ l) (hr : a.1 = b.1) : a = b := by
  have hp := pairwise_of_ranksAscend l h
  induction l with
  | nil => simp at ha
  | cons x t ih =>
    have hp' := List.pairwise_cons.1 hp
    have ht : ranksAscend t = true := ranksAscend_of_pairwise t hp'.2
    rcases List.mem_cons.1 ha with hax | hat <;> rcases List.mem_cons.1 hb with hbx | hbt
    · rw [hax, hbx]
    · rw [hax] at hr; exact absurd hr (Nat.ne_of_lt (hp'.1 b hbt))
    · rw [hbx] at hr; exact absurd hr.symm (Nat.ne_of_lt (hp'.1 a hat))
    · exact ih ht hat hbt hp'.2

theorem foldl_congr_mem {α β : Type} (f g : β → α → β) :
    ∀ (l : List α) (acc : β), (∀ b x, x ∈ l → f b x = g b x) → l.foldl f acc = l.foldl g acc
  | [], _, _ => rfl
  | x :: t, acc, h => by
    simp only [List.foldl_cons]
    rw [h acc x (List.mem_cons_self ..)]
    exact foldl_congr_mem f g t _ (fun b y hy => h b y (List.mem_cons_of_mem _ hy))

/-- **A shift at `n` does not move the section of a rank at or below `n`.** -/
theorem lastHeadingBefore_shiftFrom (d : Doc) {n r : Nat} (hr : r ≤ n) :
    lastHeadingBefore (d.shiftFrom n) r = lastHeadingBefore d r := by
  unfold lastHeadingBefore
  show (d.prose.map (fun q => (shiftRank n q.1, q.2))).foldl _ none = _
  rw [List.foldl_map]
  apply foldl_congr_mem
  intro acc q _
  by_cases hq : q.1 < n
  · have hs : shiftRank n q.1 = q.1 := by unfold shiftRank; rw [if_neg (Nat.not_le.2 hq)]
    have hl := liveHeading_shiftFrom n d q
    simp only [hs] at hl ⊢
    rw [hl]
  · have hs : shiftRank n q.1 = q.1 + 1 := by unfold shiftRank; rw [if_pos (Nat.not_lt.1 hq)]
    have h1 : ¬ (q.1 + 1 < r) := by omega
    have h2 : ¬ (q.1 < r) := by omega
    simp only [hs, h1, h2, decide_false, Bool.false_and, Bool.false_eq_true, if_false]

/-! #### The heading folds, characterised -/

def lhbStep (d : Doc) (r : Nat) (acc : Option (Nat × List Char)) (q : Nat × List Char) :
    Option (Nat × List Char) :=
  if decide (q.1 < r) && liveHeading d q then
    match acc with
    | none   => some q
    | some b => if b.1 < q.1 then some q else some b
  else acc

theorem lastHeadingBefore_eq_foldl (d : Doc) (r : Nat) :
    lastHeadingBefore d r = d.prose.foldl (lhbStep d r) none := rfl

theorem foldl_lhbStep_some (d : Doc) (r : Nat) : ∀ (l : List (Nat × List Char)) (acc : Option (Nat × List Char))
    (x : Nat × List Char), l.foldl (lhbStep d r) acc = some x →
      (acc = some x ∨ (x ∈ l ∧ x.1 < r ∧ liveHeading d x = true)) ∧
      (∀ b, acc = some b → b.1 ≤ x.1) ∧
      (∀ q ∈ l, q.1 < r → liveHeading d q = true → q.1 ≤ x.1)
  | [], acc, x, h => by
    simp only [List.foldl_nil] at h
    subst h
    exact ⟨Or.inl rfl, fun b hb => by injection hb with hb; subst hb; exact Nat.le_refl _, fun q hq => by simp at hq⟩
  | q :: t, acc, x, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2, h3⟩ := foldl_lhbStep_some d r t _ x h
    unfold lhbStep at h1 h2
    by_cases he : (decide (q.1 < r) && liveHeading d q) = true
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at he
      have he' : (decide (q.1 < r) && liveHeading d q) = true := by simp [he.1, he.2]
      rw [if_pos he'] at h1 h2
      cases acc with
      | none =>
        simp only at h1 h2
        refine ⟨?_, fun b hb => absurd hb (by simp), fun q' hq' hlt hlive => ?_⟩
        · rcases h1 with h1 | h1
          · injection h1 with h1; subst h1
            exact Or.inr ⟨List.mem_cons_self .., he.1, he.2⟩
          · exact Or.inr ⟨List.mem_cons_of_mem _ h1.1, h1.2⟩
        · rcases List.mem_cons.1 hq' with rfl | hq'
          · exact h2 _ rfl
          · exact h3 q' hq' hlt hlive
      | some b =>
        simp only at h1 h2
        by_cases hbq : b.1 < q.1
        · rw [if_pos hbq] at h1 h2
          refine ⟨?_, fun b' hb' => ?_, fun q' hq' hlt hlive => ?_⟩
          · rcases h1 with h1 | h1
            · injection h1 with h1; subst h1
              exact Or.inr ⟨List.mem_cons_self .., he.1, he.2⟩
            · exact Or.inr ⟨List.mem_cons_of_mem _ h1.1, h1.2⟩
          · injection hb' with hb'; subst hb'
            exact Nat.le_trans (Nat.le_of_lt hbq) (h2 _ rfl)
          · rcases List.mem_cons.1 hq' with rfl | hq'
            · exact h2 _ rfl
            · exact h3 q' hq' hlt hlive
        · rw [if_neg hbq] at h1 h2
          refine ⟨?_, fun b' hb' => ?_, fun q' hq' hlt hlive => ?_⟩
          · rcases h1 with h1 | h1
            · exact Or.inl h1
            · exact Or.inr ⟨List.mem_cons_of_mem _ h1.1, h1.2⟩
          · injection hb' with hb'; subst hb'
            exact h2 _ rfl
          · rcases List.mem_cons.1 hq' with rfl | hq'
            · exact Nat.le_trans (Nat.not_lt.1 hbq) (h2 _ rfl)
            · exact h3 q' hq' hlt hlive
    · simp only [Bool.not_eq_true] at he
      rw [if_neg (by simp [he])] at h1 h2
      refine ⟨?_, h2, fun q' hq' hlt hlive => ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1.1, h1.2⟩
      · rcases List.mem_cons.1 hq' with rfl | hq'
        · simp [hlt, hlive] at he
        · exact h3 q' hq' hlt hlive

theorem foldl_lhbStep_ne_none (d : Doc) (r : Nat) : ∀ (l : List (Nat × List Char)) (acc : Option (Nat × List Char)),
    (acc ≠ none ∨ ∃ q ∈ l, q.1 < r ∧ liveHeading d q = true) → l.foldl (lhbStep d r) acc ≠ none
  | [], acc, h => by
    rcases h with h | ⟨q, hq, _⟩
    · exact h
    · simp at hq
  | q :: t, acc, h => by
    simp only [List.foldl_cons]
    apply foldl_lhbStep_ne_none d r t
    by_cases he : (decide (q.1 < r) && liveHeading d q) = true
    · left
      unfold lhbStep
      rw [if_pos he]
      cases acc with
      | none => simp
      | some b => simp only; split <;> simp
    · rcases h with h | ⟨q', hq', hlt, hlive⟩
      · left
        unfold lhbStep
        rw [if_neg he]
        exact h
      · rcases List.mem_cons.1 hq' with rfl | hq'
        · simp [hlt, hlive] at he
        · right; exact ⟨q', hq', hlt, hlive⟩

/-- **The section of a rank is the live heading of greatest rank below it.** -/
theorem lastHeadingBefore_eq_of_max {d : Doc} {r : Nat} {q : Nat × List Char}
    (hasc : ranksAscend d.prose = true) (hq : q ∈ d.prose) (hlt : q.1 < r) (hlive : liveHeading d q = true)
    (hmax : ∀ q' ∈ d.prose, q'.1 < r → liveHeading d q' = true → q'.1 ≤ q.1) :
    lastHeadingBefore d r = some q := by
  rw [lastHeadingBefore_eq_foldl]
  cases hx : d.prose.foldl (lhbStep d r) none with
  | none => exact absurd hx (foldl_lhbStep_ne_none d r d.prose none (Or.inr ⟨q, hq, hlt, hlive⟩))
  | some x =>
    obtain ⟨h1, _, h3⟩ := foldl_lhbStep_some d r d.prose none x hx
    rcases h1 with h1 | ⟨hxm, hxlt, hxlive⟩
    · cases h1
    · have hle1 := h3 q hq hlt hlive
      have hle2 := hmax x hxm hxlt hxlive
      exact congrArg some (prose_eq_of_rank hasc hxm hq (Nat.le_antisymm hle2 hle1))

theorem foldl_fhaStep_some (live : Nat × List Char → Bool) (want : List Char → Bool) (lo : Option Nat) :
    ∀ (l : List (Nat × List Char)) (acc : Option Nat) (x : Nat), l.foldl (fhaStep live want lo) acc = some x →
      (acc = some x ∨ ∃ q ∈ l, live q = true ∧ want q.2 = true ∧ loOk lo q.1 = true ∧ q.1 = x) ∧
      (∀ b, acc = some b → x ≤ b) ∧
      (∀ q ∈ l, live q = true → want q.2 = true → loOk lo q.1 = true → x ≤ q.1)
  | [], acc, x, h => by
    simp only [List.foldl_nil] at h
    subst h
    exact ⟨Or.inl rfl, fun b hb => by injection hb with hb; subst hb; exact Nat.le_refl _, fun q hq => by simp at hq⟩
  | q :: t, acc, x, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2, h3⟩ := foldl_fhaStep_some live want lo t _ x h
    unfold fhaStep at h1 h2
    by_cases he : (live q && want q.2 && loOk lo q.1) = true
    · rw [if_pos he] at h1 h2
      simp only [Bool.and_eq_true] at he
      cases acc with
      | none =>
        simp only at h1 h2
        refine ⟨?_, fun b hb => absurd hb (by simp), fun q' hq' hl hw ho => ?_⟩
        · rcases h1 with h1 | ⟨q', hq', hl, hw, ho, hx⟩
          · injection h1 with h1
            exact Or.inr ⟨q, List.mem_cons_self .., he.1.1, he.1.2, he.2, h1⟩
          · exact Or.inr ⟨q', List.mem_cons_of_mem _ hq', hl, hw, ho, hx⟩
        · rcases List.mem_cons.1 hq' with rfl | hq'
          · exact h2 _ rfl
          · exact h3 q' hq' hl hw ho
      | some b =>
        simp only at h1 h2
        refine ⟨?_, fun b' hb' => ?_, fun q' hq' hl hw ho => ?_⟩
        · rcases h1 with h1 | ⟨q', hq', hl, hw, ho, hx⟩
          · injection h1 with h1
            have h1' : min b q.1 = x := h1
            rcases Nat.le_total b q.1 with hbq | hbq
            · left; rw [Nat.min_eq_left hbq] at h1'; rw [h1']
            · right; rw [Nat.min_eq_right hbq] at h1'
              exact ⟨q, List.mem_cons_self .., he.1.1, he.1.2, he.2, h1'⟩
          · exact Or.inr ⟨q', List.mem_cons_of_mem _ hq', hl, hw, ho, hx⟩
        · injection hb' with hb'; subst hb'
          exact Nat.le_trans (h2 _ rfl) (Nat.min_le_left b q.1)
        · rcases List.mem_cons.1 hq' with rfl | hq'
          · exact Nat.le_trans (h2 _ rfl) (Nat.min_le_right b _)
          · exact h3 q' hq' hl hw ho
    · simp only [Bool.not_eq_true] at he
      rw [if_neg (by simp [he])] at h1 h2
      refine ⟨?_, h2, fun q' hq' hl hw ho => ?_⟩
      · rcases h1 with h1 | ⟨q', hq', hl, hw, ho, hx⟩
        · exact Or.inl h1
        · exact Or.inr ⟨q', List.mem_cons_of_mem _ hq', hl, hw, ho, hx⟩
      · rcases List.mem_cons.1 hq' with rfl | hq'
        · simp [hl, hw, ho] at he
        · exact h3 q' hq' hl hw ho

theorem foldl_fhaStep_none (live : Nat × List Char → Bool) (want : List Char → Bool) (lo : Option Nat) :
    ∀ (l : List (Nat × List Char)) (acc : Option Nat), l.foldl (fhaStep live want lo) acc = none →
      acc = none ∧ ∀ q ∈ l, live q = true → want q.2 = true → loOk lo q.1 = true → False
  | [], acc, h => ⟨h, fun q hq => by simp at hq⟩
  | q :: t, acc, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := foldl_fhaStep_none live want lo t _ h
    unfold fhaStep at h1
    by_cases he : (live q && want q.2 && loOk lo q.1) = true
    · rw [if_pos he] at h1
      cases acc <;> simp at h1
    · rw [if_neg he] at h1
      refine ⟨h1, fun q' hq' hl hw ho => ?_⟩
      rcases List.mem_cons.1 hq' with rfl | hq'
      · simp [hl, hw, ho] at he
      · exact h2 q' hq' hl hw ho

theorem prose_rank_lt_endRank {p : PlanCore} {k : DocIx} {d : Doc} (hd : p.docs[k]? = some d)
    {q : Nat × List Char} (hq : q ∈ d.prose) : q.1 < endRank p k := by
  have hm : q.1 ∈ docRanks p k := by
    unfold docRanks
    rw [hd]
    exact List.mem_append_left _ (List.mem_map.2 ⟨q, hq, rfl⟩)
  exact Nat.lt_succ_of_le (le_foldl_max_nat _ 0 _ hm)

/-- **D7's landing is under `# Overdue`.**  Where `landingSpot` places a line for
the overdue section — the end of the file after it, or the rank of the heading
that follows it, which the shift frees — the live heading of greatest rank below
that place, in the document as the landing leaves it, is named `Overdue`. -/
theorem landingSpot_overdue_is_under_overdue {p : PlanCore} {k : DocIx} {d : Doc}
    {src : Option (List Char)} {spot : Option Nat} (hd : p.docs[k]? = some d)
    (hasc : ranksAscend d.prose = true)
    (hsp : landingSpot p k .overdueSection src = .ok spot) :
    ∃ hq, lastHeadingBefore (Doc.bump spot d) (spot.getD (endRank p k)) = some hq ∧
      headingBody hq.2 = "Overdue".toList := by
  unfold landingSpot at hsp
  rw [hd] at hsp
  simp only at hsp
  cases hh : firstHeadingAbove d none (fun h => headingBody h == "Overdue".toList) with
  | none => rw [hh] at hsp; cases hsp
  | some h =>
    rw [hh] at hsp
    simp only [Except.ok.injEq] at hsp
    rw [firstHeadingAbove_eq] at hh
    obtain ⟨hh1, _, _⟩ := foldl_fhaStep_some _ _ _ d.prose none h hh
    rcases hh1 with hh1 | ⟨qh, hqh, hlive, hwant, _, hqr⟩
    · cases hh1
    refine ⟨qh, ?_, by simpa using hwant⟩
    rw [firstHeadingAbove_eq] at hsp
    cases spot with
    | none =>
      obtain ⟨_, hnone⟩ := foldl_fhaStep_none _ _ _ d.prose none hsp
      show lastHeadingBefore d (endRank p k) = some qh
      refine lastHeadingBefore_eq_of_max hasc hqh (prose_rank_lt_endRank hd hqh) hlive
        (fun q' hq' _ hl' => ?_)
      rw [hqr]
      exact Nat.not_lt.1 (fun hc => hnone q' hq' hl' rfl (by simpa [loOk] using hc))
    | some n =>
      obtain ⟨hn1, _, hn3⟩ := foldl_fhaStep_some _ _ _ d.prose none n hsp
      rcases hn1 with hn1 | ⟨qn, hqn, _, _, hon, hqnr⟩
      · cases hn1
      have hhn : h < n := by rw [← hqnr]; simpa [loOk] using hon
      show lastHeadingBefore (d.shiftFrom n) n = some qh
      rw [lastHeadingBefore_shiftFrom d (Nat.le_refl n)]
      refine lastHeadingBefore_eq_of_max hasc hqh (by rw [hqr]; exact hhn) hlive
        (fun q' hq' hlt' hl' => ?_)
      rw [hqr]
      refine Nat.not_lt.1 (fun hc => ?_)
      have := hn3 q' hq' hl' rfl (by simpa [loOk] using hc)
      omega


/-- **One step of D7's route lands the line under `# Overdue`.** -/
theorem closeOne_lands_an_overdue_line_under_overdue {g : Grain} {now : Day} {x : FoldFx} {i : Id}
    {p q : WfPlan} (h : closeOne g now x i p = .ok q) {e : Entity} (hp : p.val.store.get i = some e)
    (hact : closeAct g now p.val e.val.skel = .overdue) :
    ∃ f hd, q.val.store.get i = some f ∧ docKindAt q.val f.val.live.doc = .backlog ∧
      sectionAt q.val f.val.live = some hd ∧ headingBody hd = "Overdue".toList := by
  obtain ⟨hfr, _, _⟩ := closeOne_spec h
  rcases closeOne_moves h with ⟨_, hst⟩ | ⟨e', k, spot, hpe, _, _, hds, ⟨f, hf, hlive⟩, _, _, hovr⟩ |
      ⟨_, _, e'', r, hpe, hA, _⟩
  · exact absurd (hst e hp) (by rw [hact]; simp)
  rotate_left
  · rw [hp] at hpe
    injection hpe with hpe
    subst hpe
    rw [hact] at hA
    cases hA
  · rw [hp] at hpe
    injection hpe with hpe
    subst hpe
    obtain ⟨hk, hsp⟩ := hovr hact
    obtain ⟨hlen, hkind, _⟩ := overdueTarget_spec hk
    obtain ⟨d, hd⟩ : ∃ d, p.val.docs[k]? = some d := ⟨_, List.getElem?_eq_getElem hlen⟩
    have hasc := prose_ranks_ascend p d (List.mem_of_getElem? hd)
    obtain ⟨hq, hlhb, hbody⟩ := landingSpot_overdue_is_under_overdue hd hasc hsp
    have hqd : q.val.docs[k]? = some (Doc.bump spot d) := by rw [hds k, if_pos rfl, hd]; rfl
    refine ⟨f, hq.2, hf, by rw [hlive, hfr.2.1]; exact hkind, ?_, hbody⟩
    unfold sectionAt
    rw [hlive]
    simp only
    rw [hqd]
    simp only [hlhb, Option.map_some]

/-- **After `i` has landed under `# Overdue`, it stays there.**  A later step lands
a line in the backlog only by the same route (a carry goes to a week, a filing to a
week or a month), at a spot above `i`, so neither `i`'s rank nor the heading above
it moves; a step elsewhere does not touch the backlog. -/
theorem fold_keeps_an_overdue_line_under_overdue (g : Grain) (now : Day) (fx : Id → FoldFx) (p0 : WfPlan)
    (i : Id) (K : DocIx) (hK : docKindAt p0.val K = .backlog) :
    ∀ (l : List Id) (P Q : WfPlan), l.foldlM (fun q c => closeOne g now (fx c) c q) P = .ok Q → i ∉ l →
      Frame p0.val P.val →
      (∃ a, P.val.store.get i = some a ∧ a.val.live.doc = K ∧
        (∃ hd, sectionAt P.val a.val.live = some hd ∧ headingBody hd = "Overdue".toList) ∧
        ∀ spot, landingSpot P.val K .overdueSection none = .ok spot → ∀ n, spot = some n →
          a.val.live.rank < n) →
      ∃ f hd, Q.val.store.get i = some f ∧ sectionAt Q.val f.val.live = some hd ∧
        headingBody hd = "Overdue".toList := by
  intro l
  induction l with
  | nil =>
    intro P Q h _ _ ha
    simp only [List.foldlM_nil] at h
    injection h with h
    subst h
    obtain ⟨a, hPa, _, ⟨hd, hs, hb⟩, _⟩ := ha
    exact ⟨a, hd, hPa, hs, hb⟩
  | cons c rest ih =>
    intro P Q h hi hfr ha
    simp only [List.foldlM_cons] at h
    cases h1 : closeOne g now (fx c) c P with
    | error x => rw [h1] at h; simp [bind, Except.bind] at h
    | ok P1 =>
      rw [h1] at h
      simp only [bind, Except.bind] at h
      have hci : i ≠ c := fun hc => hi (hc ▸ List.mem_cons_self ..)
      obtain ⟨hf1, _, _⟩ := closeOne_spec h1
      refine ih P1 Q h (fun hm => hi (List.mem_cons_of_mem _ hm)) (hfr.trans hf1) ?_
      obtain ⟨a, hPa, had, ⟨hd, hs, hb⟩, hbound⟩ := ha
      rcases closeOne_moves h1 with ⟨rfl, _⟩ | ⟨ec, k, spot, hPc, _, hjs, hds, _, hcar, hfil, hovr⟩ |
          ⟨hdocs, hlives, _⟩
      · exact ⟨a, hPa, had, ⟨hd, hs, hb⟩, hbound⟩
      rotate_left
      · have hli := hlives i
        rw [hPa] at hli
        obtain ⟨a', ha', hal⟩ := get_of_map_eq_some hli
        simp only at hal
        have hdK : ∀ d : DocIx, P1.val.docs[d]? = P.val.docs[d]? := fun d => by rw [hdocs]
        refine ⟨a', ha', by rw [hal, had], ⟨hd, ?_, hb⟩, fun spot hsp n hn => ?_⟩
        · rw [hal, sectionAt_docs (hdK _)]; exact hs
        · rw [landingSpot_docs (hdK K)] at hsp
          rw [hal]; exact hbound spot hsp n hn
      · have hli := hjs i hci
        rw [hPa] at hli
        obtain ⟨a', ha', hal⟩ := get_of_map_eq_some hli
        simp only at hal
        refine ⟨a', ha', by rw [hal, Site.bump_doc, had], ?_, spot_bound_after_step hds hal had hbound⟩
        have hKP : docKindAt P.val K = .backlog := by rw [hfr.2.1]; exact hK
        by_cases hKk : K = k
        · cases hAc : closeAct g now P.val ec.val.skel with
          | stay =>
            have hP1 : closeOne g now (fx c) c P = .ok P := by
              unfold closeOne; simp only [hPc, hAc]
            rw [hP1] at h1
            injection h1 with h1
            subst h1
            rw [hPa] at ha'
            injection ha' with ha'
            subst ha'
            exact ⟨hd, hs, hb⟩
          | carry =>
            obtain ⟨hk, _⟩ := hcar hAc
            have := (findDocIx_spec hk).2.1
            rw [← hKk, hKP] at this
            cases this
          | file r =>
            obtain ⟨hk, _⟩ := hfil r hAc
            have := (findDocIx_spec hk).2.1
            rw [← hKk, hKP] at this
            exact (kindOfGrain_is_never_backlog _ this.symm).elim
          | overdue =>
            obtain ⟨_, hsp⟩ := hovr hAc
            rw [landingSpot_src P.val k (l := .overdueSection) (by decide) _ none, ← hKk] at hsp
            have hlt := hbound spot hsp
            have hsP := hs
            unfold sectionAt at hsP
            rw [had] at hsP
            cases hdK : P.val.docs[K]? with
            | none => rw [hdK] at hsP; cases hsP
            | some d =>
              rw [hdK] at hsP
              simp only at hsP
              have hP1K : P1.val.docs[K]? = some (Doc.bump spot d) := by
                rw [hds K, if_pos hKk, hdK]; rfl
              refine ⟨hd, ?_, hb⟩
              unfold sectionAt
              rw [hal, Site.bump_doc, had, hP1K]
              simp only
              cases spot with
              | none => rw [Site.bump_none]; exact hsP
              | some m =>
                have hm := hlt m rfl
                rw [Site.bump_rank_of_doc _ (had.trans hKk)]
                show (lastHeadingBefore (d.shiftFrom m) (shiftRank m a.val.live.rank)).map Prod.snd = _
                have hsr : shiftRank m a.val.live.rank = a.val.live.rank := by
                  unfold shiftRank; rw [if_neg (Nat.not_le.2 hm)]
                rw [hsr, lastHeadingBefore_shiftFrom d (Nat.le_of_lt hm)]
                exact hsP
        · refine ⟨hd, ?_, hb⟩
          rw [hal, Site.bump_of_ne spot (by rw [had]; exact hKk)]
          have hsd : sectionAt P1.val a.val.live = sectionAt P.val a.val.live :=
            sectionAt_docs (by rw [hds _, if_neg (by rw [had]; exact hKk)])
          rw [hsd]
          exact hs


/-- **The fold, before `i` has landed**: the step that lands it puts it under
`# Overdue` with every later backlog landing above it, and the steps before it
leave it where it is. -/
theorem fold_lands_an_overdue_line_under_overdue (g : Grain) (now : Day) (fx : Id → FoldFx) (p0 : WfPlan)
    (i : Id) (ei : Entity) (hact : closeAct g now p0.val ei.val.skel = .overdue) :
    ∀ (l : List Id) (P Q : WfPlan), l.foldlM (fun q c => closeOne g now (fx c) c q) P = .ok Q →
      l.Nodup → i ∈ l → Frame p0.val P.val → ClosedDocsKept now p0.val P.val →
      (∃ a, P.val.store.get i = some a ∧ a.val.skel = ei.val.skel ∧ a.val.live = ei.val.live) →
      ∃ f hd, Q.val.store.get i = some f ∧ sectionAt Q.val f.val.live = some hd ∧
        headingBody hd = "Overdue".toList := by
  obtain ⟨r0, hr0, hc0⟩ := closeAct_closed (g := g) (now := now) (p := p0.val) (s := ei.val.skel)
    (by rw [hact]; simp)
  intro l
  induction l with
  | nil => intro _ _ _ _ hi; simp at hi
  | cons c rest ih =>
    intro P Q h hnd hi hfr hcd ha
    simp only [List.foldlM_cons] at h
    cases h1 : closeOne g now (fx c) c P with
    | error x => rw [h1] at h; simp [bind, Except.bind] at h
    | ok P1 =>
      rw [h1] at h
      simp only [bind, Except.bind] at h
      have hnd' := List.nodup_cons.1 hnd
      obtain ⟨a, hPa, has, hal⟩ := ha
      obtain ⟨hf1, _, _⟩ := closeOne_spec h1
      have hfr1 := hfr.trans hf1
      by_cases hic : i = c
      · -- the step that lands `i`
        subst hic
        have hactP := closeAct_skel_frame (g := g) (now := now) hfr has
        rcases closeOne_moves h1 with ⟨_, hst⟩ |
            ⟨e, k, spot, hPe, _, _, hds, ⟨f', hf', hlive⟩, _, _, hovr⟩ | ⟨_, _, e, r, hPe, hA, _⟩
        · exact absurd (hactP.trans hact) (by rw [hst a hPa]; simp)
        rotate_left
        · rw [hPa] at hPe
          injection hPe with hPe
          subst hPe
          rw [hactP.trans hact] at hA
          cases hA
        · rw [hPa] at hPe
          injection hPe with hPe
          subst hPe
          obtain ⟨hk, hsp⟩ := hovr (hactP.trans hact)
          obtain ⟨hlen, hkind, _⟩ := overdueTarget_spec hk
          obtain ⟨d, hd⟩ : ∃ d, P.val.docs[k]? = some d := ⟨_, List.getElem?_eq_getElem hlen⟩
          have hasc := prose_ranks_ascend P d (List.mem_of_getElem? hd)
          obtain ⟨hq, hlhb, hbody⟩ := landingSpot_overdue_is_under_overdue hd hasc hsp
          have hqd : P1.val.docs[k]? = some (Doc.bump spot d) := by rw [hds k, if_pos rfl, hd]; rfl
          have hK : docKindAt p0.val k = .backlog := by rw [← hfr.2.1]; exact hkind
          refine fold_keeps_an_overdue_line_under_overdue g now fx p0 i k hK rest P1 Q h hnd'.1 hfr1
            ⟨f', hf', by rw [hlive], ⟨hq.2, ?_, hbody⟩, ?_⟩
          · unfold sectionAt
            rw [hlive]
            simp only
            rw [hqd]
            simp only [hlhb, Option.map_some]
          · intro s1 hs1 n hn
            rw [landingSpot_src P1.val k (l := .overdueSection) (by decide) none
              (sectionAt P.val a.val.live)] at hs1
            have := landed_rank_lt_next_spot hds hsp s1 hs1 n hn
            rw [hlive]
            exact this
      · -- a step that lands some other line
        have hir : i ∈ rest := (List.mem_cons.1 hi).resolve_left hic
        obtain ⟨_, hcd1, a', ha', ha's, ha'l⟩ :=
          closeOne_keeps_untaken h1 hfr hcd hic hPa has hal hr0 hc0
        exact ih P1 Q h hnd'.2 hir hfr1 hcd1 ⟨a', ha', ha's, ha'l⟩


/-- **D7's landing, for the whole close: a line the week row routes as overdue ends
under the backlog's `# Overdue`.**  The heading it stands under — the live heading of
greatest rank above it in the file — is named `Overdue`, however many other lines
the same close lands in that section or elsewhere (`fold_lands_an_overdue_line_under_overdue`). -/
theorem close_lands_every_overdue_line_under_overdue {g : Grain} {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close g now bm p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f)
    (hact : closeAct g now p.val e.val.skel = .overdue) :
    ∃ hd, sectionAt q.val f.val.live = some hd ∧ headingBody hd = "Overdue".toList := by
  have hmi : i ∈ closeCands g now p.val := by
    by_cases hc : i ∈ closeCands g now p.val
    · exact hc
    · exact absurd (closeAct_of_not_mem_closeCands hc hp) (by rw [hact]; simp)
  obtain ⟨f', hd, hf', hs, hb⟩ := fold_lands_an_overdue_line_under_overdue g now (foldFxOf g now bm p.val)
    p i e hact (closeCands g now p.val) p q h (closeCands_nodup g now p.val) hmi (Frame.refl _)
    (fun _ _ _ _ => rfl) ⟨e, hp, rfl, rfl⟩
  rw [hq] at hf'
  injection hf' with hf'
  subst hf'
  exact ⟨hd, hs, hb⟩

/-- **D7: a past-due `persist` line is moved to the backlog's `# Overdue`, as it
was.**  A week close that takes a line past due with `persist` puts it in the
backlog — the file of kind `backlog` with no region, which no close ever takes a
line from — under the heading `# Overdue` (`close_lands_every_overdue_line_under_overdue`),
with its box, its bytes and its tombstone exactly as they were: no `demoted:`
stamp, its `due:` intact, and no `[-]` left in the week file (§6.3: "moved to
`backlog.md#Overdue` **instead**").  Decided on loaded plans in Boundary.lean
(`the_week_close_routes_dated_work_on_a_loaded_plan`,
`the_example_week_closes_with_d1_in_the_backlog_overdue`). -/
theorem close_moves_a_past_due_persist_line_to_the_backlog {g : Grain} {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close g now bm p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f)
    (hact : closeAct g now p.val e.val.skel = .overdue) :
    docKindAt q.val f.val.live.doc = .backlog ∧ docRegion q.val f.val.live.doc = none ∧
      (∃ hd, sectionAt q.val f.val.live = some hd ∧ headingBody hd = "Overdue".toList) ∧
      f.val.line = e.val.line ∧ f.val.status = e.val.status ∧
      f.val.archive.map Tomb.line = e.val.archive.map Tomb.line ∧
      f.val.archive.map (fun t => t.site.doc) = e.val.archive.map (fun t => t.site.doc) := by
  obtain ⟨hfr, hall⟩ := close_spec h
  have hsk := close_skel h hp hq
  have hst := (hall i).2 f hq
  rw [closeAct_frame hfr] at hst
  cases hk : overdueTarget p.val with
  | none =>
    have hstep : stepSkel g now p.val (foldFxOf g now bm p.val i) e.val.skel = e.val.skel := by
      unfold stepSkel; simp only [hact, hk]
    rw [hsk, hstep, hact] at hst
    exact absurd hst (by simp)
  | some k =>
    have hstep : stepSkel g now p.val (foldFxOf g now bm p.val i) e.val.skel = { e.val.skel with doc := k } := by
      unfold stepSkel; simp only [hact, hk]
    rw [hstep] at hsk
    have hdoc : f.val.live.doc = k := congrArg Skel.doc hsk
    obtain ⟨_, hkind, hreg⟩ := overdueTarget_spec hk
    refine ⟨by rw [hfr.2.1, hdoc]; exact hkind, by rw [hfr.2.2, hdoc]; exact hreg,
      close_lands_every_overdue_line_under_overdue h hp hq hact,
      congrArg Skel.line hsk, congrArg Skel.status hsk, congrArg Skel.archLine hsk,
      congrArg Skel.archDoc hsk⟩

/-- **D8: a dated line the week row files keeps its date** — a line the child fold
does not drop (restates `close_week_files_a_dated_line_keeping_its_date`, false of a
dated child dropped with its parent, which stays `[~]` in the week file:
`a_dropped_child_keeps_its_record_unmerged`, Boundary.lean).  A week close that takes
a point-dated line which is not past due with `persist` — not yet due, or past due
with `on-miss:expire`/`next` — leaves the line behind as the `[-]` tombstone in its
own bytes and files a `[-]` record into the month containing *now*, and the record's
shape is the line's: the `due:` survives the stamp (and a merged or folded estimate).
Fork-point `close_week` demotes such a line and `check.rs` has no date rule for a
month record; since D8 `shapesWf` has none either (`demotedRecordPlacement`). -/
theorem close_week_files_a_dated_line_it_does_not_drop_keeping_its_date {now : Day} {bm : Nat}
    {p q : WfPlan} (h : close week now bm p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) {r : Region}
    (hreg : closedRegionOf week now p.val e.val.live.doc = some r)
    (htakes : (closePolicy week).takes e.val.status = true) (hrec : e.val.recur = Recur.none)
    {m : Field.Moment} (hdue : e.val.shape = Shape.point m) (hnov : e.val.skel.overdue now = false)
    (hnd : dropsInto week now p.val i = none) :
    docRegion q.val f.val.live.doc = some (closeTo week now) ∧
      docKindAt q.val f.val.live.doc = .month ∧
      f.val.status = .demoted ∧ f.val.archive.map Tomb.line = some e.val.line ∧
      Stamp.week (Cal.isoOf (7 * r.ix)).week ∈ f.val.stamps ∧
      f.val.shape = e.val.shape := by
  have hrec' : e.val.skel.recurring = false := by
    show decide (Field.viewRecur e.val.line ≠ Recur.none) = false
    have : Field.viewRecur e.val.line = Recur.none := hrec
    simp [this]
  have hwall : e.val.skel.wallAhead now = none := by
    show (match Field.viewShape e.val.line with
          | .interval _ b => some (decide (now ≤ b.day))
          | _ => none) = none
    have : Field.viewShape e.val.line = Shape.point m := hdue
    rw [this]
  have hact : closeAct week now p.val e.val.skel = .file r := by
    unfold closeAct
    show (match closedRegionOf week now p.val e.val.live.doc with
          | none => CloseAct.stay
          | some r => _) = _
    rw [hreg]
    have htakes' : (closePolicy week).takes e.val.skel.status = true := htakes
    simp only [htakes', hrec', hnov, Bool.true_eq_false, Bool.false_eq_true, if_false, and_false,
      hwall]
  obtain ⟨hr, hk, hsk⟩ := close_files_a_taken_line_it_does_not_drop_into_closeTo h hp hq hact hnd
  rw [skelAfter_week] at hsk
  have hl : f.val.line = refiledLineX (foldFxOf week now bm p.val i) (.week (Cal.isoOf (7 * r.ix)).week)
      e.val.skel.archLine e.val.skel.line := congrArg Skel.line hsk
  refine ⟨hr, hk, congrArg Skel.status hsk, congrArg Skel.archLine hsk, ?_, ?_⟩
  · show _ ∈ (Field.viewDemoted f.val.line).getD []
    rw [hl]
    exact refiledLineX_stamps_mem _ _ _ _
  · show Field.viewShape f.val.line = Field.viewShape e.val.line
    rw [hl]
    exact viewShape_refiledLineX _ _ _ _

/-- **Not yet due is not overdue**: a point due on `now`'s day or later is filed by
D8's rule, whatever its `on_miss`. -/
theorem Skel.overdue_of_not_yet_due {now : Day} {c : Core} {m : Field.Moment}
    (hdue : c.shape = Shape.point m) (hnot : now ≤ m.day) : c.skel.overdue now = false := by
  cases hb : c.skel.overdue now with
  | false => rfl
  | true =>
    obtain ⟨_, ⟨m', hm', hlt⟩ | ⟨a, b, hab, _⟩⟩ := (Core.skel_overdue_iff c now).1 hb
    · rw [hdue] at hm'
      injection hm' with hm'
      subst hm'
      exact absurd hlt (Nat.not_lt.2 hnot)
    · rw [hdue] at hab; cases hab

/-- **D8, as the owner put it: a not-yet-due dated task unfinished at a week close is
demoted like any unfinished task and keeps its date** — like any unfinished task the
week row does not drop with its parent (restates
`close_week_demotes_a_not_yet_due_line_keeping_its_date`, false of such a child since
B3's repair: §6.3 drops an unfinished child of a line the close files).  `[-]` stays
behind in the week file in the line's own bytes; the record in the month containing
*now* is `[-]`, carries the closed week's stamp, and its shape — the `due:` — is the
line's.  (`close_week_files_a_dated_line_it_does_not_drop_keeping_its_date`, at a due
day on or after `now`'s.) -/
theorem close_week_demotes_a_not_yet_due_line_it_does_not_drop_keeping_its_date {now : Day} {bm : Nat}
    {p q : WfPlan} (h : close week now bm p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) {r : Region}
    (hreg : closedRegionOf week now p.val e.val.live.doc = some r)
    (htakes : (closePolicy week).takes e.val.status = true) (hrec : e.val.recur = Recur.none)
    {m : Field.Moment} (hdue : e.val.shape = Shape.point m) (hnot : now ≤ m.day)
    (hnd : dropsInto week now p.val i = none) :
    docRegion q.val f.val.live.doc = some (closeTo week now) ∧
      docKindAt q.val f.val.live.doc = .month ∧
      f.val.status = .demoted ∧ f.val.archive.map Tomb.line = some e.val.line ∧
      Stamp.week (Cal.isoOf (7 * r.ix)).week ∈ f.val.stamps ∧
      f.val.shape = e.val.shape :=
  close_week_files_a_dated_line_it_does_not_drop_keeping_its_date h hp hq hreg htakes hrec hdue
    (Skel.overdue_of_not_yet_due hdue hnot) hnd

/-- **D7, as the owner put it: a past-due dated `persist` task unfinished at a week
close goes to the backlog, as it was.**  The hypotheses in the core's own terms — a
point due, or an interval ended, on a day before `now`'s, with §5.3's effective
`on_miss` `persist` — for a line of a closed week whose box the week row takes and
which is not recurring. -/
theorem close_week_moves_a_past_due_persist_line_to_the_backlog {now : Day} {bm : Nat} {p q : WfPlan}
    (h : close week now bm p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) {r : Region}
    (hreg : closedRegionOf week now p.val e.val.live.doc = some r)
    (htakes : (closePolicy week).takes e.val.status = true) (hrec : e.val.recur = Recur.none)
    (hpersist : effectiveOnMiss e.val = .persist)
    (hpast : (∃ m, e.val.shape = Shape.point m ∧ m.day < now) ∨
      (∃ a b, e.val.shape = Shape.interval a b ∧ b.day < now)) :
    docKindAt q.val f.val.live.doc = .backlog ∧ docRegion q.val f.val.live.doc = none ∧
      (∃ hd, sectionAt q.val f.val.live = some hd ∧ headingBody hd = "Overdue".toList) ∧
      f.val.line = e.val.line ∧ f.val.status = e.val.status ∧
      f.val.archive.map Tomb.line = e.val.archive.map Tomb.line ∧
      f.val.archive.map (fun t => t.site.doc) = e.val.archive.map (fun t => t.site.doc) := by
  refine close_moves_a_past_due_persist_line_to_the_backlog h hp hq ?_
  have hrec' : e.val.skel.recurring = false := by
    show decide (Field.viewRecur e.val.line ≠ Recur.none) = false
    have : Field.viewRecur e.val.line = Recur.none := hrec
    simp [this]
  have hov : e.val.skel.overdue now = true := (Core.skel_overdue_iff e.val now).2 ⟨hpersist, hpast⟩
  unfold closeAct
  show (match closedRegionOf week now p.val e.val.live.doc with
        | none => CloseAct.stay
        | some r => _) = _
  rw [hreg]
  have htakes' : (closePolicy week).takes e.val.skel.status = true := htakes
  simp only [htakes', hrec', hov, Bool.true_eq_false, Bool.false_eq_true, if_false]
  rfl

end Tm
