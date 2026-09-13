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
53–57 for what the fold does refuse or does not write): §6.3's week-row
"dated items past due with `persist` → `backlog.md#Overdue`" (needs §5.3's
`on_miss` against `due:`, stage 5 — the `overdue` column says so), its
"unfinished children are dropped, their remaining folded into the parent's
`est:`" (needs `Core.parent`, README gap 22 — the `children` column), the day
file's review section (F3, stage 6), and `est:` = remaining beyond the line's
own reading (the log's minutes and the rollup; `demoteEst`'s inputs are not in
`close`'s signature).
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
      forward (§6.3's week row — `demote`) -/
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

/-- A §6.3 clause the fold does **not** perform, and what it waits on.  A column
of this type is how a scope-out stays visible in the table instead of in a
comment nobody reads. -/
inductive Owed
  | nothing
  /-- needs §5.3's `on_miss` evaluated against `due:` — stage 5 -/
  | stage5OnMiss
  /-- needs `Core.parent` read off the line — README gap 22, an owner decision -/
  | gap22Parent
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
  overdue     : Owed
  /-- the week row's "unfinished children are dropped … folded into the parent's `est:`" -/
  children    : Owed

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
                overdue := .nothing, children := .nothing }
  | ⟨1, _⟩ => { takes := Status.isOpenBox, disposition := .copy,
                landing := .demotedSection, stamp := .isoWeek,
                recurring := .stays, walls := .carried,
                overdue := .stage5OnMiss, children := .gap22Parent }
  | _      => { takes := Status.isUnsettled, disposition := .move,
                landing := .sameSection, stamp := .none,
                recurring := .stays, walls := .carried,
                overdue := .nothing, children := .nothing }

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
the record, and a second tombstone is `KErr.alreadyDemoted`. -/
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

/-- **The two scope-outs are in the table.**  The week row owes §6.3's overdue
routing to stage 5 and its child fold to gap 22; no other row owes either. -/
theorem closePolicy_owes :
    ∀ g : Grain, ((closePolicy g).overdue = .stage5OnMiss ↔ g = week) ∧
      ((closePolicy g).children = .gap22Parent ↔ g = week) ∧
      ((closePolicy g).overdue = .nothing ∨ (closePolicy g).overdue = .stage5OnMiss) ∧
      ((closePolicy g).children = .nothing ∨ (closePolicy g).children = .gap22Parent) := by
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
deriving DecidableEq, Repr

def exemptAct : Exemption → Bool → CloseAct
  | .stays,   _     => .stay
  | .carried, true  => .carry
  | .carried, false => .stay

/-- **The candidate set and the action, as one function of the plan's files
and the line's skeleton.**  A line not in a closed region of grain `g` stays; so
does one whose box the row does not take.  A recurring line and a wall get their
exemption; everything else is filed. -/
def closeAct (g : Grain) (now : Day) (p : PlanCore) (s : Skel) : CloseAct :=
  match closedRegionOf g now p s.doc with
  | none   => .stay
  | some r =>
    if (closePolicy g).takes s.status = false then .stay
    else if s.recurring then exemptAct (closePolicy g).recurring true
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

/-- §6.3's day row: `[>]` → `[ ]`. -/
def reopen : Status → Status
  | .live .self => .live .free
  | s           => s

/-- The bytes with a stamp appended, if the row names one. -/
def stampedLine (os : Option Stamp) (s : Skel) : RawItem :=
  match os with
  | none    => s.line
  | some st => Field.setDemoted (s.stamps ++ [st]) s.line

/-- The skeleton filing a line out of region `r` into document `k` leaves. -/
def skelAfter (g : Grain) (r : Region) (k : DocIx) (s : Skel) : Skel :=
  match (closePolicy g).disposition with
  | .move          => { s with doc := k }
  | .moveReopening => { s with doc := k, status := reopen s.status,
                               line := stampedLine (closeStamp g r.ix) s }
  | .copy          =>
    match closeStamp g r.ix with
    | some st => ⟨k, some s.doc, some s.line, .demoted, Field.setDemoted (s.stamps ++ [st]) s.line⟩
    | none    => s

/-- **The denotation of one step, on a skeleton.**  The branches with no
target are the ones in which `close` refuses; they return the skeleton
unchanged, which no theorem below reads. -/
def stepSkel (g : Grain) (now : Day) (p : PlanCore) (s : Skel) : Skel :=
  match closeAct g now p s with
  | .stay   => s
  | .carry  =>
    match carryTarget now p with
    | some k => { s with doc := k }
    | none   => s
  | .file r =>
    match closeTarget g now p with
    | some k => skelAfter g r k s
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
table's disposition, through the command algebra's own transforms. -/
def fileE (g : Grain) (r : Region) (t : Site) (e : Entity) : Except KErr Entity :=
  match (closePolicy g).disposition with
  | .move          => moveTo t e
  | .moveReopening => lift { e.val with live := t, status := reopen e.val.status,
                                        line := stampedLine (closeStamp g r.ix) e.val.skel }
  | .copy          =>
    match closeStamp g r.ix with
    | some st => demote t st e
    | none    => .error .badHorizon

/-! ## `close` -/

/-- **One step**: close id `i` of the plan it is handed. -/
def closeOne (g : Grain) (now : Day) (i : Id) : Transform := fun p =>
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
      match closeTarget g now p.val with
      | none   => .error .noTarget
      | some k =>
        match landingSpot p.val k (closePolicy g).landing (sectionAt p.val e.val.live) with
        | .error x => .error x
        | .ok spot => landAt p k spot i (fileE g r)

/-- The ids a close of grain `g` at `now` acts on, in store order. -/
def closeCands (g : Grain) (now : Day) (p : PlanCore) : List Id :=
  p.store.dom.filter (fun i =>
    match p.store.get i with
    | none   => false
    | some e =>
      match closeAct g now p e.val.skel with
      | .stay => false
      | _     => true)

/-- **§6.3's lifecycle at one grain**: fold `closeOne` over the candidates.
The provisional `Goals.close` signature, made real — the grain, the instant,
`Transform` as the shape, and `ClosePolicy` read from the table rather than
passed. -/
def close (g : Grain) (now : Day) : Transform := fun p =>
  (closeCands g now p.val).foldlM (fun q i => closeOne g now i q) p

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

theorem fileE_skel {g : Grain} {r : Region} {t : Site} {e f : Entity}
    (h : fileE g r t e = .ok f) : f.val.skel = skelAfter g r t.doc e.val.skel ∧ f.val.live = t := by
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
      have hv := demote_roundtrips _ _ _ _ h
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

theorem stepSkel_frame {p q : PlanCore} (hf : Frame p q) (g : Grain) (now : Day) (s : Skel) :
    stepSkel g now q s = stepSkel g now p s := by
  unfold stepSkel carryTarget closeTarget
  rw [closeAct_frame hf, findDocIx_frame hf, findDocIx_frame hf]

theorem findDocIx_spec {p : PlanCore} {kind : DocKind} {r : Region} {k : DocIx}
    (h : findDocIx p kind r = some k) :
    k < p.docs.length ∧ docKindAt p k = kind ∧ docRegion p k = some r := by
  unfold findDocIx at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨List.mem_range.1 hm, hp.1, hp.2⟩

/-- A line in a file whose region is open is not one any close takes. -/
theorem closeAct_of_open {p : PlanCore} {g : Grain} {now : Day} {s : Skel} {r : Region}
    (hr : docRegion p s.doc = some r) (ho : ¬ Closed r now) : closeAct g now p s = .stay := by
  unfold closeAct closedRegionOf
  rw [hr]
  simp [ho]

theorem closeOne_spec {g : Grain} {now : Day} {i : Id} {p q : WfPlan}
    (h : closeOne g now i p = .ok q) :
    Frame p.val q.val ∧
      (∀ j, j ≠ i → (q.val.store.get j).map (fun e => e.val.skel) =
        (p.val.store.get j).map (fun e => e.val.skel)) ∧
      ∃ e f, p.val.store.get i = some e ∧ q.val.store.get i = some f ∧
        f.val.skel = stepSkel g now p.val e.val.skel ∧ closeAct g now p.val f.val.skel = .stay := by
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
      · simp at h
      · rename_i k hk
        split at h
        · simp at h
        · rename_i spot _
          obtain ⟨hfr, hj, e0, e', t, f', hget0, hsk, htd, hfe, hq⟩ := landAt_spec h
          rw [hget] at hget0
          injection hget0 with hget0
          subst hget0
          obtain ⟨hfs, hlive⟩ := fileE_skel hfe
          refine ⟨hfr, hj, e, f', hget, hq, ?_, ?_⟩
          · rw [hfs, hsk, htd]
            unfold stepSkel
            rw [hact, hk]
          · obtain ⟨_, _, hreg⟩ := findDocIx_spec hk
            refine closeAct_of_open (r := closeTo g now) ?_ (closeTo_target_is_open g now)
            show docRegion p.val f'.val.live.doc = _
            rw [hlive, htd]
            exact hreg

/-! ## The fold -/

theorem foldlM_closeOne_spec (g : Grain) (now : Day) (p0 : WfPlan) :
    ∀ (l : List Id) (p q : WfPlan) (done : List Id),
      l.Nodup → (∀ i ∈ l, i ∉ done) → Frame p0.val p.val →
      (∀ j, j ∉ done → (p.val.store.get j).map (fun e => e.val.skel) =
        (p0.val.store.get j).map (fun e => e.val.skel)) →
      (∀ j, j ∈ done → ∃ e f, p0.val.store.get j = some e ∧ p.val.store.get j = some f ∧
        f.val.skel = stepSkel g now p0.val e.val.skel ∧
        closeAct g now p0.val f.val.skel = .stay) →
      l.foldlM (fun q i => closeOne g now i q) p = .ok q →
      Frame p0.val q.val ∧
        (∀ j, j ∉ done → j ∉ l → (q.val.store.get j).map (fun e => e.val.skel) =
          (p0.val.store.get j).map (fun e => e.val.skel)) ∧
        (∀ j, j ∈ done ∨ j ∈ l → ∃ e f, p0.val.store.get j = some e ∧
          q.val.store.get j = some f ∧ f.val.skel = stepSkel g now p0.val e.val.skel ∧
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
    cases h1 : closeOne g now i p with
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
  p.store.domNodup.filter _

theorem closeAct_of_not_mem_closeCands {g : Grain} {now : Day} {p : PlanCore} {j : Id} {e : Entity}
    (hj : j ∉ closeCands g now p) (hget : p.store.get j = some e) :
    closeAct g now p e.val.skel = .stay := by
  cases hact : closeAct g now p e.val.skel with
  | stay => rfl
  | carry =>
    exfalso; apply hj
    refine List.mem_filter.2 ⟨(p.store.domSpec j).2 (by rw [hget]; rfl), ?_⟩
    rw [hget]; simp only [hact]
  | file r =>
    exfalso; apply hj
    refine List.mem_filter.2 ⟨(p.store.domSpec j).2 (by rw [hget]; rfl), ?_⟩
    rw [hget]; simp only [hact]

/-- **The denotation of `close`.**  A successful close keeps every file's kind
and region, turns every id's skeleton into `stepSkel` of what it was, and leaves
no line that a close of the same grain at the same instant would take again. -/
theorem close_spec {g : Grain} {now : Day} {p q : WfPlan} (h : close g now p = .ok q) :
    Frame p.val q.val ∧
      ∀ j, (q.val.store.get j).map (fun e => e.val.skel) =
          (p.val.store.get j).map (fun e => stepSkel g now p.val e.val.skel) ∧
        ∀ f, q.val.store.get j = some f → closeAct g now q.val f.val.skel = .stay := by
  have hf := foldlM_closeOne_spec g now p (closeCands g now p.val) p q []
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
      have hstep : stepSkel g now p.val e.val.skel = e.val.skel := by
        unfold stepSkel; rw [hst]
      refine ⟨by rw [hm]; simp [hstep], fun f hf => ?_⟩
      rw [hf] at hm
      simp only [Option.map_some, Option.some.injEq] at hm
      rw [closeAct_frame hfr, hm]
      exact hst

/-- **`close_skel`**: the per-id reading of `close_spec`, with both lookups
named. -/
theorem close_skel {g : Grain} {now : Day} {p q : WfPlan} (h : close g now p = .ok q)
    {i : Id} {e f : Entity} (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) :
    f.val.skel = stepSkel g now p.val e.val.skel := by
  have := ((close_spec h).2 i).1
  rw [hp, hq] at this
  simpa using this


/-! ## What a close guarantees, read off `close_spec` -/

theorem exemptAct_cases (x : Exemption) (b : Bool) :
    exemptAct x b = .stay ∨ exemptAct x b = .carry := by
  cases x <;> cases b <;> simp [exemptAct]

/-- A recurring line and a wall are never *filed*: whatever the table's
exemption column says, `exemptAct` has no `file` branch. -/
theorem closeAct_of_exempt {g : Grain} {now : Day} {p : PlanCore} {s : Skel}
    (hx : s.recurring = true ∨ ∃ b, s.wallAhead now = some b) :
    closeAct g now p s = .stay ∨ closeAct g now p s = .carry := by
  unfold closeAct
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · split
      · exact exemptAct_cases _ _
      · rename_i hrec
        rcases hx with hx | ⟨b, hb⟩
        · exact absurd hx hrec
        · rw [hb]; exact exemptAct_cases _ _

theorem stepSkel_of_exempt {g : Grain} {now : Day} {p : PlanCore} {s : Skel}
    (hx : closeAct g now p s = .stay ∨ closeAct g now p s = .carry) :
    stepSkel g now p s = { s with doc := (stepSkel g now p s).doc } := by
  unfold stepSkel
  rcases hx with hx | hx
  · rw [hx]
  · rw [hx]
    cases carryTarget now p <;> rfl

/-- Where `stepSkel` files a line, it names the line's new file — or it is the
unreachable copy-without-a-stamp branch and leaves the skeleton alone. -/
theorem skelAfter_doc (g : Grain) (r : Region) (k : DocIx) (s : Skel) :
    (skelAfter g r k s).doc = k ∨ skelAfter g r k s = s := by
  unfold skelAfter
  cases (closePolicy g).disposition with
  | move => exact Or.inl rfl
  | moveReopening => exact Or.inl rfl
  | copy => cases closeStamp g r.ix <;> simp

/-- **Narrowed L18** (`close_leaves_no_live_line_in_a_closed_region`, which is
stated over every line and so over the `[x]` lines §6.3 leaves in an archive;
refuted as `close_leaves_live_lines_in_a_closed_region`, Boundary.lean).
After a close, no line is one the same close would take: every line still in a
closed region of grain `g` is settled, recurring, a wall, or of a box the row
does not take. -/
theorem close_leaves_no_line_it_would_take {g : Grain} {now : Day} {p q : WfPlan}
    (h : close g now p = .ok q) (i : Id) (f : Entity) (hq : q.val.store.get i = some f) :
    closeAct g now q.val f.val.skel = .stay :=
  ((close_spec h).2 i).2 f hq

/-- The same, unpacked into the goal's own shape, with the narrowing in the
hypotheses where a reader can see it: a line of the grain's own file kind, whose
box the row takes, that is neither recurring nor a wall, is not in a closed
region of that grain after the close. -/
theorem close_leaves_no_unfinished_line_in_a_closed_region {g : Grain} {now : Day}
    {p q : WfPlan} (h : close g now p = .ok q) (i : Id) (f : Entity)
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
  simp [htakes', hrec', hwall'] at hst

theorem stepSkel_day_stamps (now : Day) (p : PlanCore) (s : Skel) :
    (stepSkel day now p s).stamps = s.stamps ∨
      ∃ n, (stepSkel day now p s).stamps = s.stamps ++ [Stamp.day n] := by
  unfold stepSkel
  split
  · exact Or.inl rfl
  · split <;> exact Or.inl rfl
  · rename_i r _
    split
    · refine Or.inr ⟨(Cal.ofDay r.ix).day, ?_⟩
      show (Field.viewDemoted (Field.setDemoted (s.stamps ++ [Stamp.day (Cal.ofDay r.ix).day])
        s.line)).getD [] = _
      rw [Field.view_set_demoted _ _ (by simp)]
      rfl
    · exact Or.inl rfl

/-- **§6.3's day row stamps a day stamp** (discharged from `Goals.lean`).  A day
close that changes a line's stamps appends exactly one, and it is a `D` stamp —
so the month review's "≥ 2 stamps" cut list, which counts `W` stamps, cannot be
fed a day's leftovers as if they were a week's. -/
theorem close_day_stamps_a_day_stamp (now : Day) (p q : WfPlan)
    (h : close day now p = .ok q) (i : Id) (e f : Entity)
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f)
    (hchanged : f.val.stamps ≠ e.val.stamps) :
    ∃ n : Nat, f.val.stamps = e.val.stamps ++ [Stamp.day n] := by
  have hsk := close_skel h hp hq
  rcases stepSkel_day_stamps now p.val e.val.skel with hs | hs
  · exact absurd (by rw [← Core.skel_stamps, hsk, hs]; rfl) hchanged
  · obtain ⟨n, hn⟩ := hs
    exact ⟨n, by rw [← Core.skel_stamps, hsk, hn]; rfl⟩

theorem stepSkel_line (g : Grain) (now : Day) (p : PlanCore) (s : Skel) :
    (stepSkel g now p s).line = s.line ∨
      ∃ ss, (stepSkel g now p s).line = Field.setDemoted ss s.line := by
  unfold stepSkel
  split
  · exact Or.inl rfl
  · split <;> exact Or.inl rfl
  · rename_i r _
    split
    · unfold skelAfter
      cases (closePolicy g).disposition with
      | move => exact Or.inl rfl
      | moveReopening =>
        simp only
        unfold stampedLine
        cases closeStamp g r.ix with
        | none => exact Or.inl rfl
        | some st => exact Or.inr ⟨_, rfl⟩
      | copy =>
        cases closeStamp g r.ix with
        | none => exact Or.inl rfl
        | some st => exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl

/-- **Narrowed B1–B3** (`close_writes_every_estimate_through_demoteEst`, which
equates the whole line with `demoteEst`'s and so forbids the `demoted:` stamp
§6.3 appends; refuted as `close_writes_a_line_demoteEst_does_not`, Boundary.lean).
A close rewrites a line's bytes in one way only: it sets the
`demoted:` token.  It writes no estimate at all — `est:` = remaining beyond the
line's own reading needs the log and the rollup, which `close` does not have —
so no measurement standing on the line is replaced. -/
theorem close_rewrites_a_line_only_by_stamping_it {g : Grain} {now : Day} {p q : WfPlan}
    (h : close g now p = .ok q) (i : Id) (e f : Entity)
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) :
    f.val.line = e.val.line ∨ ∃ ss, f.val.line = Field.setDemoted ss e.val.line := by
  have hsk := close_skel h hp hq
  have := stepSkel_line g now p.val e.val.skel
  rw [← hsk] at this
  exact this

/-- **The estimate half of narrowed B1–B3.**  Whatever a close does to a line, its
remaining estimate is the one it had, at every block length: the only rewrite is
the `demoted:` stamp (`close_rewrites_a_line_only_by_stamping_it`) and a stamp is
invisible to `remainingOf` (`Field.remainingOf_setDemoted`).  So a close is the
identity on estimates — exactly `demoteEst bm true`'s reading, and never a
replacement of a measurement standing on the line. -/
theorem close_keeps_every_remaining_estimate {g : Grain} {now : Day} {p q : WfPlan}
    (h : close g now p = .ok q) (i : Id) (e f : Entity)
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) (bm : Nat) :
    remainingOf bm f.val.line = remainingOf bm e.val.line := by
  rcases close_rewrites_a_line_only_by_stamping_it h i e f hp hq with hl | ⟨ss, hl⟩
  · rw [hl]
  · rw [hl, Field.remainingOf_setDemoted]

/-- **Narrowed F4** (`close_never_demotes_a_wall`, whose `f.val = e.val` forbids
the carry — and the rank shift a landing inside a section performs; refuted as
`close_does_not_leave_every_wall_as_it_was`, Boundary.lean).  A
recurring line or a wall keeps its box, its bytes and its tombstone through
every close; the one thing that may change is the file its record is in. -/
theorem close_never_demotes_a_wall_but_may_carry_it {g : Grain} {now : Day} {p q : WfPlan}
    (h : close g now p = .ok q) (i : Id) (e f : Entity)
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
  have := stepSkel_of_exempt (closeAct_of_exempt (g := g) (p := p.val) hx)
  rw [hsk]
  conv => lhs; rw [this]
  rw [← hsk]
  rfl

/-- **D1, as a theorem.**  A line a close takes is filed into `closeTo g now` —
the file of the next coarser grain containing *now* — and its skeleton is the
table's row applied to it.  Never `targetContaining`: see the next theorem. -/
theorem close_files_a_taken_line_into_closeTo {g : Grain} {now : Day} {p q : WfPlan}
    (h : close g now p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) {r : Region}
    (hact : closeAct g now p.val e.val.skel = .file r) :
    docRegion q.val f.val.live.doc = some (closeTo g now) ∧
      docKindAt q.val f.val.live.doc = kindOfGrain (coarsen g) ∧
      f.val.skel = skelAfter g r f.val.live.doc e.val.skel := by
  obtain ⟨hfr, hall⟩ := close_spec h
  have hsk := close_skel h hp hq
  have hst := (hall i).2 f hq
  rw [closeAct_frame hfr] at hst
  cases hk : closeTarget g now p.val with
  | none =>
    have hstep : stepSkel g now p.val e.val.skel = e.val.skel := by
      unfold stepSkel; simp only [hact, hk]
    rw [hsk, hstep, hact] at hst
    exact absurd hst (by simp)
  | some k =>
    have hstep : stepSkel g now p.val e.val.skel = skelAfter g r k e.val.skel := by
      unfold stepSkel; simp only [hact, hk]
    rw [hstep] at hsk
    rcases skelAfter_doc g r k e.val.skel with hd | hd
    · have hdoc : f.val.live.doc = k := by
        have := congrArg Skel.doc hsk
        rw [hd] at this
        exact this
      obtain ⟨_, hkind, hreg⟩ := findDocIx_spec hk
      refine ⟨by rw [hfr.2.2, hdoc]; exact hreg, by rw [hfr.2.1, hdoc]; exact hkind, ?_⟩
      rw [hdoc]; exact hsk
    · rw [hsk, hd, hact] at hst
      exact absurd hst (by simp)

/-- **D1 separates from the rule it replaced.**  A day close files into the
week containing *now*; whenever the closed day's week is not now's week — a
close run late — that is not the week the closed day belonged to
(`targetContaining`, fork-point `horizon::close_day`). -/
theorem close_day_files_into_the_week_of_now {now : Day} {p q : WfPlan}
    (h : close day now p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) {r : Region}
    (hact : closeAct day now p.val e.val.skel = .file r)
    (hlate : Cal.weekOrdinal r.ix ≠ Cal.weekOrdinal now) :
    docRegion q.val f.val.live.doc = some (closeTo day now) ∧
      docRegion q.val f.val.live.doc ≠ some (targetContaining day r.ix) := by
  have ⟨hreg, _, _⟩ := close_files_a_taken_line_into_closeTo h hp hq hact
  refine ⟨hreg, ?_⟩
  rw [hreg]
  intro hc
  injection hc with hc
  exact (impl_rule_disagrees_iff day r.ix now).2 hlate hc.symm

/-- **F4's carry.**  A wall still ahead, in a closed region a close takes it
from, lands in the live week — the one week file the planner reads (§6.2) —
with its box, bytes and tombstone untouched. -/
theorem close_carries_a_wall_that_is_still_ahead {g : Grain} {now : Day} {p q : WfPlan}
    (h : close g now p = .ok q) {i : Id} {e f : Entity}
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
    simp [htakes', hrec', hw, (closePolicy_exemptions g).2, exemptAct]
  cases hk : carryTarget now p.val with
  | none =>
    have hstep : stepSkel g now p.val e.val.skel = e.val.skel := by
      unfold stepSkel; simp only [hact, hk]
    rw [hsk, hstep, hact] at hst
    exact absurd hst (by simp)
  | some k =>
    have hstep : stepSkel g now p.val e.val.skel = { e.val.skel with doc := k } := by
      unfold stepSkel; simp only [hact, hk]
    rw [hstep] at hsk
    have hdoc : f.val.live.doc = k := congrArg Skel.doc hsk
    obtain ⟨_, hkind, hreg'⟩ := findDocIx_spec hk
    refine ⟨by rw [hfr.2.2, hdoc]; exact hreg', by rw [hfr.2.1, hdoc]; exact hkind, ?_⟩
    rw [hsk, hdoc]

/-! ## The check bites: every refusal is named, none is a skip -/

/-- A line to file and no document to file it into is `noTarget`. -/
theorem closeOne_refuses_a_missing_target {g : Grain} {now : Day} {i : Id} {p : WfPlan}
    {e : Entity} {r : Region} (hget : p.val.store.get i = some e)
    (hact : closeAct g now p.val e.val.skel = .file r)
    (hnone : closeTarget g now p.val = none) : closeOne g now i p = .error .noTarget := by
  unfold closeOne
  simp only [hget, hact, hnone]

/-- A wall to carry and no live week to carry it into is `noTarget` too — the
close does not leave it stranded in the archive and call that success. -/
theorem closeOne_refuses_a_carry_with_no_live_week {g : Grain} {now : Day} {i : Id}
    {p : WfPlan} {e : Entity} (hget : p.val.store.get i = some e)
    (hact : closeAct g now p.val e.val.skel = .carry)
    (hnone : carryTarget now p.val = none) : closeOne g now i p = .error .noTarget := by
  unfold closeOne
  simp only [hget, hact, hnone]

/-- A destination with no section to receive the line is `noSection`. -/
theorem closeOne_refuses_a_missing_section {g : Grain} {now : Day} {i : Id} {p : WfPlan}
    {e : Entity} {r : Region} {k : DocIx} (hget : p.val.store.get i = some e)
    (hact : closeAct g now p.val e.val.skel = .file r) (hk : closeTarget g now p.val = some k)
    (hsec : landingSpot p.val k (closePolicy g).landing (sectionAt p.val e.val.live) =
      .error .noSection) : closeOne g now i p = .error .noSection := by
  unfold closeOne
  simp only [hget, hact, hk, hsec]

/-- **The post-state check bites.**  A filed line whose post-state fails
`planWf` — a dated item filed into a month file that holds outcomes only, a
tombstone the loader could not orient — is refused as `badHorizon`, and nothing
is written. -/
theorem closeOne_refuses_an_ill_formed_post_state {g : Grain} {now : Day} {i : Id}
    {p : WfPlan} {e f : Entity} {r : Region} {k : DocIx}
    (hget : p.val.store.get i = some e)
    (hact : closeAct g now p.val e.val.skel = .file r) (hk : closeTarget g now p.val = some k)
    (hspot : landingSpot p.val k (closePolicy g).landing (sectionAt p.val e.val.live) = .ok none)
    (hf : fileE g r ⟨k, endRank p.val k⟩ e = .ok f)
    (hbad : ¬ planWf { p.val with store := p.val.store.set i f (by rw [hget]; rfl) } = true) :
    closeOne g now i p = .error .badHorizon := by
  unfold closeOne
  simp only [hget, hact, hk, hspot]
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

/-- **A second demotion is refused by the close, too.**  §6.3's week row on an
item that already carries a tombstone — §4.3's own pre-close pair, a `[ ]`
record in a week beside its `[-]` copy in a month — is `alreadyDemoted`:
re-filing it needs `demoteEst`'s floor over the standing copy's `est:`, whose
inputs `close` does not have (README gap 53). -/
theorem closeOne_week_refuses_a_standing_tombstone {now : Day} {i : Id} {p : WfPlan}
    {e : Entity} {r : Region} {k : DocIx} (hget : p.val.store.get i = some e)
    (hact : closeAct week now p.val e.val.skel = .file r) (hk : closeTarget week now p.val = some k)
    (hspot : landingSpot p.val k .demotedSection (sectionAt p.val e.val.live) = .ok none)
    (harch : e.val.archive.isSome = true) : closeOne week now i p = .error .alreadyDemoted := by
  have hl : (closePolicy week).landing = .demotedSection := rfl
  have hfe : fileE week r ⟨k, endRank p.val k⟩ e = .error .alreadyDemoted :=
    demote_on_a_standing_tombstone_is_refused _ _ e harch
  unfold closeOne
  simp only [hget, hact, hk, hl, hspot]
  unfold landAt
  simp only
  unfold WfPlan.mapAt
  split
  · rename_i hn; rw [hget] at hn; simp at hn
  · rename_i a hget'
    rw [hget] at hget'
    injection hget' with hget'
    subst hget'
    rw [hfe]

/-- **A refusal is the close's refusal.**  The fold does not skip a step that
fails: the first candidate's refusal is the whole close's answer, and no later
step runs. -/
theorem close_refuses_what_its_first_step_refuses {g : Grain} {now : Day} {p : WfPlan}
    {i : Id} {rest : List Id} {x : KErr} (hc : closeCands g now p.val = i :: rest)
    (h1 : closeOne g now i p = .error x) : close g now p = .error x := by
  show (closeCands g now p.val).foldlM (fun q i => closeOne g now i q) p = _
  rw [hc, List.foldlM_cons, h1]
  rfl


/-- **The other direction: a close with nothing to take succeeds and writes
nothing.**  An empty candidate set is the identity, not a refusal. -/
theorem close_without_candidates_is_the_identity {g : Grain} {now : Day} {p : WfPlan}
    (h : closeCands g now p.val = []) : close g now p = .ok p := by
  show (closeCands g now p.val).foldlM (fun q i => closeOne g now i q) p = _
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
  unfold closeCands
  rw [List.filter_eq_nil_iff]
  intro i _
  cases hg : p.store.get i with
  | none => simp
  | some e => simp [h i e hg]

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

**Why it holds.**  After the fold every line either stayed or was filed into
`closeTo g now` or carried into the live week, and neither region is closed
(`closeTo_target_is_open`, `regionOf_is_open`, read through
`close_leaves_no_line_it_would_take`); so the second run's candidate set is
empty and the fold is the identity (`close_without_candidates_is_the_identity`).
That is the target D1 chose; see the README's stage-4 step-3 block for where the
rule it replaced would and would not have broken this argument.

**The hypothesis is satisfiable** on loaded plans at all three grains:
`the_week_close_copies_carries_and_leaves_the_rest`,
`the_day_close_files_into_the_week_of_now` and
`the_month_close_moves_each_line_into_its_section` (Boundary.lean) each decide a
successful close. -/
theorem close_is_idempotent (g : Grain) (now : Day) (p q : WfPlan)
    (h : close g now p = .ok q) : close g now q = .ok q :=
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

theorem stepSkel_of_stay {g : Grain} {now : Day} {p : PlanCore} {s : Skel}
    (h : closeAct g now p s = .stay) : stepSkel g now p s = s := by
  unfold stepSkel; rw [h]

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

/-- **Where a step puts a line, no close of any grain at the same instant takes
it from.**  Either the step left the skeleton alone, or the file it now names is
`closeTo g now` or the live week, and neither is closed — the D1 fact L16 and
this section both run on, stated once for every pair of grains. -/
theorem stepSkel_lands_outside_every_closed_region (g g' : Grain) (now : Day) (p : PlanCore)
    (s : Skel) :
    stepSkel g now p s = s ∨ closedRegionOf g' now p (stepSkel g now p s).doc = none := by
  have hopen : ∀ k r, docRegion p k = some r → ¬ Closed r now →
      closedRegionOf g' now p k = none := by
    intro k r hr ho
    unfold closedRegionOf
    rw [hr]
    simp [ho]
  unfold stepSkel
  split
  · exact Or.inl rfl
  · split
    · rename_i k hk
      obtain ⟨_, _, hreg⟩ := findDocIx_spec hk
      exact Or.inr (hopen k _ hreg (regionOf_is_open week now))
    · exact Or.inl rfl
  · rename_i r _
    split
    · rename_i k hk
      obtain ⟨_, _, hreg⟩ := findDocIx_spec hk
      rcases skelAfter_doc g r k s with hd | hd
      · right; rw [hd]; exact hopen k _ hreg (closeTo_target_is_open g now)
      · exact Or.inl hd
    · exact Or.inl rfl

/-- One line's skeleton, closed at two grains against one plan's files, comes
out the same in either order (at one grain the two sides are one expression). -/
theorem stepSkel_comm (g g' : Grain) (now : Day) (p : PlanCore) (s : Skel) :
    stepSkel g' now p (stepSkel g now p s) = stepSkel g now p (stepSkel g' now p s) := by
  by_cases hne : g = g'
  · rw [hne]
  by_cases hg : closeAct g now p s = .stay
  · rw [stepSkel_of_stay hg]
    rcases stepSkel_lands_outside_every_closed_region g' g now p s with ht | ht
    · rw [ht, stepSkel_of_stay hg]
    · rw [stepSkel_of_stay (closeAct_of_closedRegionOf_none ht)]
  · have hg' := closeAct_of_another_grain hne hg
    rw [stepSkel_of_stay hg']
    rcases stepSkel_lands_outside_every_closed_region g g' now p s with ht | ht
    · rw [ht, stepSkel_of_stay hg']
    · rw [stepSkel_of_stay (closeAct_of_closedRegionOf_none ht)]

/-- Two closes in sequence, per id: the skeleton is the second grain's step of
the first grain's step, both read against the *starting* plan's files. -/
theorem close_bind_close_skel {g g' : Grain} {now : Day} {p q : WfPlan}
    (h : (close g now p).bind (close g' now) = .ok q) (j : Id) :
    (q.val.store.get j).map (fun e => e.val.skel) =
      (p.val.store.get j).map
        (fun e => stepSkel g' now p.val (stepSkel g now p.val e.val.skel)) := by
  cases h1 : close g now p with
  | error x => rw [h1] at h; exact absurd h (by simp [Except.bind])
  | ok q1 =>
    rw [h1] at h
    have h2 : close g' now q1 = .ok q := h
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

/-- **L17's commuting half.**  Closing two grains at the same instant, in either
order, leaves every id with the same skeleton — the same file, the same tombstone
file and bytes, the same box and the same bytes — whenever both orders succeed.
(For one grain twice the two orders are one expression; the content is at
distinct grains.)  Neither order sees the other's output, because every
destination is open (`stepSkel_lands_outside_every_closed_region`).  What this
does **not** say, and what is false (`close_week_and_close_month_do_not_commute`),
is that the two plans are equal: ranks in a shared destination depend on which
close landed first.  `close_week_month_orders_both_succeed_and_differ`
(Boundary.lean) exhibits both hypotheses, at week and month, on a loaded plan. -/
theorem two_closes_at_one_instant_commute_on_skeletons {g g' : Grain} {now : Day}
    {p q r : WfPlan}
    (hgg : (close g now p).bind (close g' now) = .ok q)
    (hgg' : (close g' now p).bind (close g now) = .ok r) (j : Id) :
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
    | some e => simp only [Option.map_some, stepSkel_comm g g' now]

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
def autoClose (now : Day) : Transform := fun p =>
  autoCloseOrder.foldlM (fun q g => close g now q) p

/-- **L19a (discharged from `Goals.lean`, as stated).**  `autoClose` is exactly
"close each grain once, coarsest last": no loop, no bound, and no
`none`-versus-`some` case anywhere but inside each close's own candidate set. -/
theorem autoClose_is_each_grain_once (now : Day) (p : WfPlan) :
    autoClose now p
      = (close day now p).bind (fun q => (close week now q).bind (close month now)) := by
  show ([day, week, month] : List Grain).foldlM (fun q g => close g now q) p = _
  simp only [List.foldlM_cons, List.foldlM_nil]
  cases h1 : close day now p with
  | error x => rfl
  | ok q1 =>
    show (close week now q1 >>= fun q => close month now q >>= fun q' => pure q') =
      (close week now q1).bind (close month now)
    cases h2 : close week now q1 with
    | error x => rfl
    | ok q2 =>
      show (close month now q2 >>= fun q' => pure q') = close month now q2
      cases close month now q2 <;> rfl

/-- A successful `autoClose`, unpacked into its three closes. -/
theorem autoClose_ok {now : Day} {p q : WfPlan} (h : autoClose now p = .ok q) :
    ∃ q1 q2, close day now p = .ok q1 ∧ close week now q1 = .ok q2 ∧ close month now q2 = .ok q := by
  rw [autoClose_is_each_grain_once] at h
  cases h1 : close day now p with
  | error x => rw [h1] at h; exact absurd h (by simp [Except.bind])
  | ok q1 =>
    rw [h1] at h
    cases h2 : close week now q1 with
    | error x =>
      have h' : (close week now q1).bind (close month now) = .ok q := h
      rw [h2] at h'; exact absurd h' (by simp [Except.bind])
    | ok q2 =>
      have h' : (close week now q1).bind (close month now) = .ok q := h
      rw [h2] at h'
      exact ⟨q1, q2, rfl, h2, h'⟩

/-- **The check bites: a refusal refuses the whole call.**  If any of the three
closes refuses, `autoClose` returns that refusal — there is no plan in which
some grain was run and the rest were stamped done. -/
theorem autoClose_refuses_what_a_grain_refuses {now : Day} {p : WfPlan} {x : KErr}
    (h : autoClose now p = .error x) :
    close day now p = .error x ∨
      ∃ q1, close day now p = .ok q1 ∧
        (close week now q1 = .error x ∨
          ∃ q2, close week now q1 = .ok q2 ∧ close month now q2 = .error x) := by
  rw [autoClose_is_each_grain_once] at h
  cases h1 : close day now p with
  | error y => rw [h1] at h; exact Or.inl h
  | ok q1 =>
    rw [h1] at h
    refine Or.inr ⟨q1, rfl, ?_⟩
    have h' : (close week now q1).bind (close month now) = .error x := h
    cases h2 : close week now q1 with
    | error y => rw [h2] at h'; exact Or.inl h'
    | ok q2 => rw [h2] at h'; exact Or.inr ⟨q2, rfl, h'⟩

/-- Every close refusal reaches `autoClose` unchanged when it is the day's. -/
theorem autoClose_refuses_a_refused_day_close {now : Day} {p : WfPlan} {x : KErr}
    (h : close day now p = .error x) : autoClose now p = .error x := by
  rw [autoClose_is_each_grain_once, h]
  rfl

/-- No line of the plan is one a close of grain `g` at `now` would take. -/
def NothingToClose (g : Grain) (now : Day) (p : WfPlan) : Prop :=
  ∀ i f, p.val.store.get i = some f → closeAct g now p.val f.val.skel = .stay

/-- **A close of any grain leaves nothing new for a close of any other.**  What
the close moved lands outside every closed region, and what it did not move
kept its skeleton against unchanged files. -/
theorem close_keeps_nothing_to_close {g g' : Grain} {now : Day} {p q : WfPlan}
    (h : close g' now p = .ok q) (hp : NothingToClose g now p) : NothingToClose g now q := by
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
    rcases stepSkel_lands_outside_every_closed_region g' g now p.val e.val.skel with ht | ht
    · rw [ht]; exact hp i e hpi
    · exact closeAct_of_closedRegionOf_none ht

/-- After a successful `autoClose`, no line is one a close of **any** grain at
that instant would take. -/
theorem autoClose_leaves_nothing_to_close {now : Day} {p q : WfPlan}
    (h : autoClose now p = .ok q) (g : Grain) : NothingToClose g now q := by
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
theorem autoClose_catches_up_in_one_step (now : Day) (p q : WfPlan)
    (h : autoClose now p = .ok q) : autoClose now q = .ok q := by
  have hs := autoClose_leaves_nothing_to_close h
  rw [autoClose_is_each_grain_once,
    close_without_candidates_is_the_identity (closeCands_eq_nil_of_stay (hs day))]
  show (close week now q).bind (close month now) = _
  rw [close_without_candidates_is_the_identity (closeCands_eq_nil_of_stay (hs week))]
  exact close_without_candidates_is_the_identity (closeCands_eq_nil_of_stay (hs month))

/-- **Narrowed L19c** (`autoClose_runs_every_period_it_passes`, which says no
live line of any kind stays in a closed region, and is refuted in Boundary.lean
by the `[x]`, recurring and done-outcome lines §6.3 leaves behind).  After
`autoClose`, a line in a closed region of its file's own grain is settled or of
a box that grain's row does not take, recurring, or a wall that is already over:
**nothing unfinished is stranded, at any grain, however stale the tree** — the
owner's three-month case, where fork-point `auto_close` ran no day close at all. -/
theorem autoClose_strands_no_unfinished_line {now : Day} {p q : WfPlan}
    (h : autoClose now p = .ok q) (i : Id) (f : Entity)
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
  simp only [htakes', hrec'] at hst
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
`stepSkel g` of that, read against `p0`'s files. -/
theorem close_skel_after {g : Grain} {now : Day} {p0 p q : WfPlan} (F : Skel → Skel)
    (hf0 : Frame p0.val p.val)
    (hpre : ∀ j, (p.val.store.get j).map (fun e => e.val.skel) =
      (p0.val.store.get j).map (fun e => F e.val.skel))
    (h : close g now p = .ok q) :
    Frame p0.val q.val ∧ ∀ j, (q.val.store.get j).map (fun e => e.val.skel) =
      (p0.val.store.get j).map (fun e => stepSkel g now p0.val (F e.val.skel)) := by
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

/-- **`autoClose`, per id**: three steps against the starting plan's files. -/
theorem autoClose_skel {now : Day} {p q : WfPlan} (h : autoClose now p = .ok q)
    {i : Id} {e f : Entity} (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) :
    f.val.skel = stepSkel month now p.val (stepSkel week now p.val (stepSkel day now p.val e.val.skel)) := by
  obtain ⟨q1, q2, h1, h2, h3⟩ := autoClose_ok h
  have s1 := close_skel_after (p0 := p) id (Frame.refl _) (fun _ => rfl) h1
  have s2 := close_skel_after (fun s => stepSkel day now p.val s) s1.1 s1.2 h2
  have s3 := close_skel_after (fun s => stepSkel week now p.val (stepSkel day now p.val s)) s2.1 s2.2 h3
  have := s3.2 i
  rw [hp, hq] at this
  simpa using this

/-- Three grains' steps on one line are one grain's step: whichever step moves
the line puts it where no later grain takes it from. -/
theorem stepSkel_three_is_one (now : Day) (P : PlanCore) (s : Skel) :
    ∃ g : Grain, stepSkel month now P (stepSkel week now P (stepSkel day now P s)) =
      stepSkel g now P s := by
  rcases stepSkel_lands_outside_every_closed_region day week now P s with h1 | h1
  · rw [h1]
    rcases stepSkel_lands_outside_every_closed_region week month now P s with h2 | h2
    · rw [h2]; exact ⟨month, rfl⟩
    · rw [stepSkel_of_stay (closeAct_of_closedRegionOf_none h2)]; exact ⟨week, rfl⟩
  · rw [stepSkel_of_stay (closeAct_of_closedRegionOf_none h1)]
    rcases stepSkel_lands_outside_every_closed_region day month now P s with h3 | h3
    · rw [h3]; exact ⟨month, rfl⟩
    · rw [stepSkel_of_stay (closeAct_of_closedRegionOf_none h3)]; exact ⟨day, rfl⟩

/-- **Each line is taken at most once by `autoClose`.**  Its skeleton afterwards
is one grain's step of what it was — never a day close's filing re-filed by the
week close, the fork-point double take of a tree fourteen days stale. -/
theorem autoClose_takes_each_line_at_most_once {now : Day} {p q : WfPlan}
    (h : autoClose now p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) :
    ∃ g : Grain, f.val.skel = stepSkel g now p.val e.val.skel := by
  obtain ⟨g, hg⟩ := stepSkel_three_is_one now p.val e.val.skel
  exact ⟨g, (autoClose_skel h hp hq).trans hg⟩

/-- One step appends at most one stamp, at any grain. -/
theorem stepSkel_stamps (g : Grain) (now : Day) (p : PlanCore) (s : Skel) :
    (stepSkel g now p s).stamps = s.stamps ∨
      ∃ st, (stepSkel g now p s).stamps = s.stamps ++ [st] := by
  have hset : ∀ st : Stamp,
      (Field.viewDemoted (Field.setDemoted (s.stamps ++ [st]) s.line)).getD [] = s.stamps ++ [st] := by
    intro st
    rw [Field.view_set_demoted _ _ (by simp)]
    rfl
  unfold stepSkel
  split
  · exact Or.inl rfl
  · split <;> exact Or.inl rfl
  · rename_i r _
    split
    · unfold skelAfter
      cases (closePolicy g).disposition with
      | move => exact Or.inl rfl
      | moveReopening =>
        simp only
        unfold stampedLine
        cases closeStamp g r.ix with
        | none => exact Or.inl rfl
        | some st => exact Or.inr ⟨st, hset st⟩
      | copy =>
        cases closeStamp g r.ix with
        | none => exact Or.inl rfl
        | some st => exact Or.inr ⟨st, hset st⟩
    · exact Or.inl rfl

/-- **F1's double stamp, ruled out.**  Across one `autoClose`, however stale the
tree, a line gains at most one stamp. -/
theorem autoClose_stamps_each_line_at_most_once {now : Day} {p q : WfPlan}
    (h : autoClose now p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) :
    f.val.stamps = e.val.stamps ∨ ∃ st, f.val.stamps = e.val.stamps ++ [st] := by
  obtain ⟨g, hg⟩ := autoClose_takes_each_line_at_most_once h hp hq
  rw [← Core.skel_stamps, ← Core.skel_stamps, hg]
  exact stepSkel_stamps g now p.val e.val.skel

end Tm
