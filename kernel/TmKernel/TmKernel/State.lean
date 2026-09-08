import TmKernel.Line
/-!
# Entity versus observation

**An id names an entity; a line is an observation of it at a site.**  That
distinction is the whole answer to the bug class.

`horizon::move_line → move_to` (horizon.rs:943) appends a line to a file
without asking whether that file already holds the id.  The `against` spike
found 426 depth-2 command pairs reachable on `main` that end in a
duplicate id, all funnelling through that one missing precondition.

Here **there is no append**, because item lines are not stored anywhere.  An
entity owns exactly one live placement and at most one archive placement, and
the lines are *rendered* from it.  A command can only replace a `Site`; putting
a second line of one id into one file is not an operation that exists.

Well-formedness is a **decidable predicate on a plain record** and the entity
is the subtype.  A per-field dependent proof gives a sharper goal but stops
`{c with …}` from working (the `firstprinciples` spike recorded this, and the
architecture note reproduced it); the subtype keeps record update *and* makes
the check unforgettable.

## §3.1's item fields are the line, and there is one `Shape`

Stage two built the whole of §4.1's field grammar in `Line.lean`'s `Field`
namespace — `Field.Shape`, `Field.Recur`, `Field.Rule`, `Field.Rate`,
`Field.Dep`, `Field.Loc`, `Field.Stamp`, a view per key and `viewFields` over
all twenty-seven.  This module used to carry its **own** copies of those types,
re-encoded over `Instant := Nat` and `Dur := Nat`, and nothing joined the two.
The consequence was measured, not argued: every calendar line in the corpus —
including §4.3's own `at:2026-09-07T12:50/13:50` — was refused with
`itemCheck: fileKindShape`, because `at:` produced a `Field.Interval` that
`Core.shape` could not see.  Two definitions of `Shape` in one kernel is
exactly how the Rust core came to have `est:` and the leading estimate
disagreeing, and it is E3/E4 in the architecture note.

So the copies are **deleted**, not bridged, and the join is not a map between
two types but the absence of the second type:

* §3.1's value types **are** §4.1's.  `Shape`, `Recur`, `Rule`, `Rate`,
  `Period`, `OnMiss`, `Dep`, `WindowRange`, `Loc`, `Stamp`, `Dur`, `DT`,
  `Moment` and `Clock` are opened from `Field`; there is one of each in the
  kernel and the import order permits it, because `State.lean` imports
  `Line.lean` and can therefore name what `Line.lean` declares.
* §3.1's item fields are **views of `line`**, not slots beside it.  `Core`
  stores four things — where the live line is, where the tombstone is, the
  status, and the token vector — and `Core.shape`, `Core.recur`, `Core.budget`,
  `Core.after`, `Core.loc`, `Core.buffer`, `Core.stamps`, `Core.waiting`,
  `Core.tags`, `Core.ci`, `Core.prio`, `Core.flags`, `Core.scope`,
  `Core.splittable`, `Core.extra`, `Core.title` and `Core.est` are functions
  that read it.  This is what `est` already did (§3.1's
  `est`/`est_original` are one slot and a reader, because two stored copies of
  one estimate is the shipped `tm edit est=` bug); every other field now does
  the same.  A stored field can drift from the bytes it was read from.  A view
  cannot, and `the_fields_are_the_line` says so as a theorem instead of a
  convention.

Four of §3.1's twenty-two fields are still absent, each for a stated reason:

* `id` is the **store key**.  "An id names one item" is what `Store.get` being
  a function means, so it is not a field of the thing being named.
* `horizon` is the **file** the item sits in (`Site.doc`).  A stored horizon is
  a second answer to a question the placement already answers — S2.
* `src` is `live` plus `line`: the token vector *is* the source text, and
  `serialize_parse` says so.
* `series` (§3.1: "from the `## series:<name>` section") and `effective_shape`
  (§3.2) are facts about the document and the tree, derived in Plan.lean.

`parent` is the **one** field still stored, and always `none`.  Deriving it
from the line's `@parent` is a two-line change and it is deliberately not made
here: §6.1 says "a week item may be a child of a month item", `parentsTotal`
(Plan.lean) is a *load precondition* rather than `tm check`'s `@ghost` report
(§17.2), and so the moment `@O2` on a week line is read, a document set that is
one file stops loading.  Every week and backlog file of the corpus would go
from `ok` to `danglingParent`.  Which of the two moves — deriving the field, or
demoting `parentsTotal` to a report — is the right one is a question about the
plan tier, not about this module; it is README gap 22.
-/
namespace Tm

/-! §4.1's value types, opened by name rather than copied.  The list is
deliberately explicit: a blanket `open Field` would also pull in `setEst`,
which this kernel already has at `Tm` scope with a different type. -/

open Field (Shape Recur Rule Rate Period OnMiss Dep WindowRange Loc Stamp Dur DT Moment Clock
  Fields Flag)

abbrev DocIx := Nat

/-- Where a line sits: which document, and its line order within it (§7.4's
rank).  There is no `horizon` field: an item's horizon **is** its file. -/
structure Site where
  doc  : DocIx
  rank : Nat
deriving DecidableEq, Repr, Inhabited

/-! ## The states a box can be in

§6.3's `[-]` is **two** things and the first version of this module saw only
one of them.

* On the *live* line of a half-finished demotion it is positional: the entity
  has a tombstone somewhere, and the box says so.  That is what `glyphAt` reads
  off `archive`.
* On a line that stands alone it is a **state**.  `tm close week` writes
  `[-]` into the week file *and* copies the line to `month/<current>#Demoted`
  (§6.3), and `tm close month` then carries that copy into the next month file
  while touching nothing else — so a month file's `# Demoted` section holds a
  `[-]` line whose partner is in a file the host may not have handed over at
  all.  §4.3's own `month/2026-09.md` is exactly that.  The Rust core agrees
  and is blunter about it: `State::Demoted` is a variant of the state enum
  (`model.rs`), `is_archive_copy` is a predicate on **one** item, and a key
  group of size one short-circuits before any pairing is attempted
  (`tree.rs`).

So there are six states, not five, and the sixth is the one the corpus found:
every `# Demoted` section in the fixture corpus was refused with
`orphanDemotion` by a loader that could not name a lone `[-]`. -/
inductive Outcome | done | dropped
deriving DecidableEq, Repr
inductive Holder | free | self | world
deriving DecidableEq, Repr
inductive Status
  | settled (o : Outcome)
  | live (h : Holder)
  /-- §6.3's archive copy standing on its own: `[-]` with no partner in this
  document set. -/
  | demoted
deriving DecidableEq, Repr

/-! ## The bounded values, and where they live now

`Clock`, the weekday and the month day were built here as `Fin`s so that
`win:25:00-…` would not be a value the kernel could hold.  §4.1's grammar
builds the same guarantee out of the same discipline — `Field.Clock` is the
same `Fin 1440`, `Cal.Weekday` has seven constructors and no numeric slot, and
`Field.parseMonthDay` is the only door into `every:month:<d>` — so the second
copy is gone and these three facts are restated about the surviving
constructors.  They are the reason `--energy 9` and `win:25:00` have nowhere to
land. -/

theorem clock_rejects_25h : Field.mkClock? 25 0 = none := by decide
theorem clock_rejects_minute_60 : Field.mkClock? 23 60 = none := by decide
theorem clock_accepts_2330 : (Field.mkClock? 23 30).map Fin.val = some 1410 := by decide

/-- There is no seventh weekday, and no numeric one either: `every:` reads the
seven names and nothing else. -/
theorem weekday_rejects_7 : Field.parseWeekday ['7'] = none := by decide

theorem monthDay_rejects_0  : Field.parseMonthDay ['0'] = none := by decide
theorem monthDay_rejects_32 : Field.parseMonthDay ['3','2'] = none := by decide

/-- And the days of a month that do exist survive the round trip, as the rule
they name. -/
theorem monthDay_roundtrips (n : Nat) (h1 : 0 < n) (h2 : n ≤ 31) :
    Field.parseRule (Field.renderRule (Rule.monthly n)) = some (Rule.monthly n) :=
  Field.parse_render_rule _ (by simp only [Field.Rule.wf, decide_eq_true_eq]; omega)

/-- §3.1's `Budget`: a floor (`min:`), a cap (`max:`), either or both.  This is
the one value type §4.1 has no single token for — `min:` and `max:` are two
keys — so it is the one that is assembled here rather than opened. -/
structure Budget where
  floor : Option Rate := Option.none
  cap   : Option Rate := Option.none
deriving DecidableEq, Repr, Inhabited

/-- §3.1's `Scope`.  `open` is a Lean keyword, hence the spelling. -/
inductive Scope | finite | openEnded
deriving DecidableEq, Repr, Inhabited

/-- Deduplicate, keeping the last occurrence of each word. -/
def dedupTags : List (List Char) → List (List Char)
  | []     => []
  | t :: r => if t ∈ dedupTags r then dedupTags r else t :: dedupTags r

theorem dedupTags_mem (l : List (List Char)) (t : List Char) : t ∈ dedupTags l ↔ t ∈ l := by
  induction l with
  | nil => simp [dedupTags]
  | cons a s ih =>
      show t ∈ (if a ∈ dedupTags s then dedupTags s else a :: dedupTags s) ↔ _
      by_cases h : a ∈ dedupTags s
      · rw [if_pos h]
        constructor
        · intro hm; exact List.mem_cons.2 (Or.inr (ih.1 hm))
        · intro hm
          rcases List.mem_cons.1 hm with rfl | hm'
          · exact h
          · exact ih.2 hm'
      · rw [if_neg h]; simp only [List.mem_cons, ih]

theorem dedupTags_nodup (l : List (List Char)) : (dedupTags l).Nodup := by
  induction l with
  | nil => simp [dedupTags]
  | cons a s ih =>
      show ((if a ∈ dedupTags s then dedupTags s else a :: dedupTags s) : List _).Nodup
      by_cases h : a ∈ dedupTags s
      · rw [if_pos h]; exact ih
      · rw [if_neg h]; exact List.nodup_cons.2 ⟨h, ih⟩

/-- §3.1's `tags`, as a **set**.  The architecture's structural tier says tags
are a set and not a `Vec` someone remembers to `dedup` — that forgetting is
E3/E4.  The `Nodup` proof lives inside the *field's own type*, so nothing else
has to carry it. -/
abbrev TagSet := { l : List (List Char) // l.Nodup }

/-- The only way to build one from raw words: duplicates cannot survive. -/
def TagSet.ofList (l : List (List Char)) : TagSet := ⟨dedupTags l, dedupTags_nodup l⟩

theorem TagSet.mem_ofList (l : List (List Char)) (t : List Char) :
    t ∈ (TagSet.ofList l).val ↔ t ∈ l := dedupTags_mem l t

/-- **A duplicated tag cannot be held**, so `#lean #lean` is one tag and no
code has to remember to dedup it. -/
theorem TagSet.no_duplicates (s : TagSet) : s.val.Nodup := s.property

/-- The observable content of one entity.  Four slots: where the live line is,
where the tombstone is if there is one, the status, and the **verbatim token
vector** (§4.2), which is where every one of §3.1's item fields lives.  See the
module header for why `parent` is the exception. -/
structure Core where
  live      : Site
  archive   : Option Site      -- at most one tombstone a close left behind
  status    : Status
  line      : RawItem
  /-- §3.1 `parent`.  Not yet read off the line — README gap 22, and the module
  header says why.  Totality and acyclicity are **plan-level** (Plan.lean):
  they are facts about the whole store, not about one record. -/
  parent    : Option Id := Option.none
deriving DecidableEq, Repr

/-! ## §3.1's item fields, as views of the line

One function per field, and it is the only thing that reads that field.  Each
is §4.1's view of the same bytes, so there is nothing for a second reader to
disagree with. -/

/-- All twenty-seven of §4.1's fields at once — the same value `renderItem`
round-trips (`field_round_trip`, Line.lean). -/
def Core.fields (c : Core) : Fields := Field.viewFields c.line

/-- §3.1 `title`: the title segment plus §4.1's unclassifiable words, which
"stay in the title". -/
def Core.title (c : Core) : List (List Char) := Field.titleWords c.line

/-- §3.1 `ci: u8` — min-energy 0–5.  **`Option`, because §3.1's rule is
"default: parent's, else 3"**: a stored 3 cannot be told from an inherited one,
and the inheritance is derived in Plan.lean (`effectiveCi`).  `viewCi` is
§4.1's C2: the `ci:` key overrides the positional digit. -/
def Core.ci (c : Core) : Option (Fin 6) := Field.viewCi c.line

/-- §3.1 `priority: Option<u8>`, explicit `!k` with k in 1–4, held
zero-based.  §3.2's `root_priority` walks to the root for it. -/
def Core.prio (c : Core) : Option (Fin 4) := Field.prioOf c.line

/-- §4.1's five flag words. -/
def Core.flags (c : Core) : List Flag := Field.flagsOf c.line

/-- §3.1 `scope`: `Finite` (default) or `Open`, and the `open` flag is the only
thing that says which.  Derived rather than stored, so `open` cannot be on the
line and off the record. -/
def Core.scope (c : Core) : Scope :=
  if Flag.openEnded ∈ c.flags then .openEnded else .finite

/-- §3.1 `splittable`: default true; the `atomic` flag sets it false. -/
def Core.splittable (c : Core) : Bool := !(Flag.atomic ∈ c.flags)

/-- §3.1 `shape`, §4.1's `at:` / `win:`+`dur:` / `due:` with `build_item`'s
precedence between them (`shape_at_wins`, Line.lean). -/
def Core.shape (c : Core) : Shape := Field.viewShape c.line

/-- §3.1 `recur`: `every:` outranks `after-done:` outranks `on-event:`.

**Recurrence is syntax, and that is a decision, not an omission.**  A `Recur`
modelled as `Log → DateTime → Option Occurrence` is not serialisable, not
`DecidableEq`, and not writable in a Markdown line — and §0 says the Markdown is
the database.  The denotation (§5.1's `instances`) is stage 5 and is
deliberately **not** here. -/
def Core.recur (c : Core) : Recur := Field.viewRecur c.line

/-- The `on-miss:` **override** only.  §5.3's default is a function of the
shape (`defaultOnMiss`), so a resolved value would be a second copy of a
derived fact. -/
def Core.onMiss (c : Core) : Option OnMiss := Field.viewOnMiss c.line

/-- §3.1 `budget`: `min:` and `max:`, the two keys §4.1 gives it. -/
def Core.budget (c : Core) : Budget := ⟨Field.viewMin c.line, Field.viewMax c.line⟩

/-- §3.1 `after`: `after:^id` or `after:event:<name>` (§5.5).  Absent is the
empty list — §4.1 has no `after:` with no dependencies (`depsWf`). -/
def Core.after (c : Core) : List Dep := (Field.viewAfter c.line).getD []

/-- §3.1's `Loc`.  §4.1's four names plus `Named`; the architecture refuses to
collapse them because *admission* is the only query. -/
def Core.loc (c : Core) : Option Loc := Field.viewLoc c.line

/-- §4.1 `buffer:` — intervals only; blocked time before start. -/
def Core.buffer (c : Core) : Option Dur := Field.viewBuffer c.line

/-- §3.1's `stamps.demoted`: `demoted:W36,W37`, newest last.  A `Stamp` knows
its grain, so a week close's `W37` and a day close's `D07` are different
values and not two readings of one number. -/
def Core.stamps (c : Core) : List Stamp := (Field.viewDemoted c.line).getD []

/-- §3.1's `stamps.waiting_since`: `waiting:<date>`. -/
def Core.waiting (c : Core) : Option Nat := Field.viewWaiting c.line

/-- §3.1 `tags`, deduplicated on the way in. -/
def Core.tags (c : Core) : TagSet := TagSet.ofList (Field.tagWords c.line)

/-- §3.1 `extra`: the unknown `key:value` tokens, preserved verbatim. -/
def Core.extra (c : Core) : List (List Char × List Char) := Field.extraPairs c.line

/-- §3.1's `est`, which is §4.1's C1: the `est:` key overrides the leading
estimate, and there is one reader so the two cannot disagree. -/
def Core.est (c : Core) : Option Dur := Field.viewRemainingDur c.line

/-- §3.2's `!k`, read out one-based the way the file writes it. -/
def Core.priorityK (c : Core) : Option Nat := c.prio.map (fun k => k.val + 1)

/-- **The fields are the line.**  Two records carrying the same token vector
carry the same §3.1 fields, whatever else differs — so there is no second copy
of an estimate, a shape or a stamp for a command to leave behind.  This is the
statement the old `Core` could not make: it had thirteen slots beside `line`,
and `demote` wrote a stamp into one of them that `renderCore` never printed.

It is true by construction, and that is the point: it fails the moment anyone
adds a slot back.  `Negative.lean`'s CHEAT 32 and CHEAT 33 are the two ways of
adding one. -/
theorem the_fields_are_the_line (c d : Core) (h : c.line = d.line) :
    c.fields = d.fields ∧ c.title = d.title ∧ c.ci = d.ci ∧ c.prio = d.prio ∧
      c.flags = d.flags ∧ c.scope = d.scope ∧ c.splittable = d.splittable ∧
      c.shape = d.shape ∧ c.recur = d.recur ∧ c.onMiss = d.onMiss ∧
      c.budget = d.budget ∧ c.after = d.after ∧ c.loc = d.loc ∧ c.buffer = d.buffer ∧
      c.stamps = d.stamps ∧ c.waiting = d.waiting ∧ c.tags = d.tags ∧
      c.extra = d.extra ∧ c.est = d.est := by
  obtain ⟨_, _, _, ln, _⟩ := c
  obtain ⟨_, _, _, ln', _⟩ := d
  have hl : ln = ln' := h
  subst hl
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩

/-! ### The fields the loader reads are §4.1's views of the bytes it read

`Core.fields` of a record built from a line is `viewFields` of that line, on
the nose.  Everything below is `rfl`; they are here because "on the nose" is
the property that broke — §3.1's copies were *reachable* from §4.1's values and
simply never reached. -/

/-- The record a loader builds from one line, with no partner.  Named so the
theorems below have something to talk about. -/
def coreOfLine (site : Site) (st : Status) (r : RawItem) : Core :=
  { live := site, archive := none, status := st, line := r }

/-- Just the fields, at an arbitrary placement: the shorthand the `decide`d
readings below use. -/
def readLine (r : RawItem) : Core := coreOfLine ⟨0, 0⟩ (.live .free) r

theorem coreOfLine_fields (site : Site) (st : Status) (r : RawItem) :
    (coreOfLine site st r).fields = Field.viewFields r := rfl
theorem coreOfLine_shape (site : Site) (st : Status) (r : RawItem) :
    (coreOfLine site st r).shape = Field.viewShape r := rfl
theorem coreOfLine_recur (site : Site) (st : Status) (r : RawItem) :
    (coreOfLine site st r).recur = Field.viewRecur r := rfl
theorem coreOfLine_stamps (site : Site) (st : Status) (r : RawItem) :
    (coreOfLine site st r).stamps = (Field.viewDemoted r).getD [] := rfl

set_option maxRecDepth 8000 in
/-- **§4.3's own calendar line, read.**  This is the line the corpus refused:
`at:` parsed and produced a `Field.Shape.interval`, and `Core.shape` — a
different type in a different namespace — stayed `none`, so §4.3's "generated
intervals" rule refused a line whose shape it could not see.  It is `decide`d,
so the kernel rechecks it on every build. -/
theorem the_spec_calendar_line_is_an_interval :
    (readLine (Field.itemOf
        "- [ ] 3 Meeting w/ host      at:2026-09-07T12:50/13:50 loc:zoom ^g1".toList)).shape =
      Shape.interval ⟨Cal.toDay ⟨2026, 9, 7⟩, ⟨12 * 60 + 50, by decide⟩⟩
                     ⟨Cal.toDay ⟨2026, 9, 7⟩, ⟨13 * 60 + 50, by decide⟩⟩ := by
  decide

set_option maxRecDepth 8000 in
/-- And the rest of that line is read too — `loc:zoom` is a location, not a
word the title swallowed. -/
theorem the_spec_calendar_line_has_a_loc :
    (readLine (Field.itemOf
        "- [ ] 3 Meeting w/ host      at:2026-09-07T12:50/13:50 loc:zoom ^g1".toList)).loc
      = some (Loc.named ['z','o','o','m']) := by decide

set_option maxRecDepth 8000 in
/-- §4.3's `# Demoted` record, read: `demoted:W37` is a **week** stamp and not
the number 37, and the `est:` override is the estimate. -/
theorem the_spec_demoted_line_is_read_whole :
    (readLine (Field.itemOf
        "- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2".toList)).stamps
        = [Stamp.week 37]
      ∧ (readLine (Field.itemOf
          "- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2".toList)).est
        = some (Dur.simple 3 .blocks) := by
  decide

set_option maxRecDepth 8000 in
/-- §4.1's own header line, read as §3.1's fields: a cap, a due date, a tag and
a ci, off one line, with no second copy of anything. -/
theorem the_spec_item_line_is_read_whole :
    (readLine Field.specItem).budget
        = ⟨Option.none, some ⟨Dur.simple 2 .blocks, Period.day⟩⟩
      ∧ (readLine Field.specItem).ci = some ⟨4, by decide⟩
      ∧ (readLine Field.specItem).est = some (Dur.simple 1 .blocks)
      ∧ (readLine Field.specItem).tags.val = [['l','e','a','n']]
      ∧ (readLine Field.specItem).shape
          = Shape.point (Moment.dateTime (Cal.toDay ⟨2026, 9, 11⟩)
              ⟨23 * 60 + 59, by decide⟩) := by
  decide

/-! ### The round trip, through §3.1's fields

`field_round_trip` (Line.lean) says a `Fields` the kernel writes reads back as
itself.  Joined here at the level of the entity: take a `Fields`, lay it out,
and read §3.1's fields off the `Core` a loader would build from those bytes —
you have the `Fields` you started with.  Because `Core` has no slot for a field
beside the line, that is the *whole* of §3.1 and not the part somebody
remembered to copy across. -/

theorem core_fields_round_trip (i : Id) (site : Site) (st : Status) (f : Fields)
    (h : Fields.canonicalWf i f = true) :
    (coreOfLine site st (Field.renderItem i f)).fields = f :=
  Field.field_round_trip i f (by
    simp only [Fields.canonicalWf, Bool.and_eq_true] at h; exact h.1)

/-! ## Well-formedness, locally -/

/-- The *local* half of the id-uniqueness invariant: the tombstone is never in
the same file as the live line.  Decidable, so the obligation is discharged by
computation and never by a proof someone has to write. -/
def wfPair (live : Site) (arch : Option Site) : Bool :=
  match arch with
  | none   => true
  | some r => r.doc != live.doc

@[simp] theorem wfPair_none (l : Site) : wfPair l none = true := rfl
@[simp] theorem wfPair_some (l r : Site) : wfPair l (some r) = (r.doc != l.doc) := rfl

def wf (c : Core) : Bool := wfPair c.live c.archive

@[simp] theorem wf_eq (c : Core) : wf c = wfPair c.live c.archive := rfl

/-- **Widening the entity does not touch the tier structure**, and this is the
whole reason the design is `Bool` + `Subtype`.  `wf` reads `live` and `archive`;
setting the slot every one of §3.1's item fields now lives in — the token
vector — therefore re-discharges *nothing*, and the proof is `rfl`.  A record
with a dependent proof field mentioning one of these would have made every one
of these updates a new obligation — the failure the `firstprinciples` spike
recorded and the architecture spike reproduced in eight places.

It is a **stronger** statement than the thirteen-binder version it replaces:
that one listed the fields it was safe to set, and this one covers every field
there is, because there is only one left to set. -/
theorem wf_ignores_the_item_fields (c : Core) (l : RawItem) (pa : Option Id) :
    wf { c with line := l, parent := pa } = wf c := rfl

/-- **The entity.**  You cannot make one without discharging `wf`. -/
def Entity := { c : Core // wf c = true }

instance : DecidableEq Entity := fun a b =>
  decidable_of_iff (a.val = b.val)
    (by constructor <;> intro h; exact Subtype.ext h; exact congrArg _ h)

/-! ## §5.3's `on_miss` default -/

/-- §5.3's default `on_miss`, **derived from one sentence**: a window is a
chance that passes, so missing it expires the instance; anything carrying a date
persists until you re-date it or drop it.  The table's four rows are that
sentence at four `(shape, recur)` pairs — and rows 3 and 4 differ *only* in
`recur` and give the same answer, which is why the generator does not read
`recur` at all. -/
def defaultOnMiss (s : Shape) : OnMiss :=
  match s with
  | .window _ _ => .expire
  | _           => .persist

/-- §5.3 row 1. -/
theorem onMiss_interval (a b : DT) : defaultOnMiss (.interval a b) = .persist := rfl
/-- §5.3 row 2. -/
theorem onMiss_point (d : Moment) : defaultOnMiss (.point d) = .persist := rfl
/-- §5.3 rows 3 and 4 — one answer, whatever the recurrence says. -/
theorem onMiss_window (r : WindowRange) (d : Dur) : defaultOnMiss (.window r d) = .expire := rfl

/-- The value the planner uses: the `on-miss:` token if the line carries one,
otherwise §5.3's default. -/
def effectiveOnMiss (c : Core) : OnMiss := c.onMiss.getD (defaultOnMiss c.shape)

/-- §5.3 rows 5 and 6: an explicit `on-miss:` always wins.  The override now
comes off the **line**, so the hypothesis is a fact about bytes and not about a
slot somebody remembered to set. -/
theorem effectiveOnMiss_override (c : Core) (m : OnMiss) (h : c.onMiss = some m) :
    effectiveOnMiss c = m := by simp [effectiveOnMiss, h]

theorem effectiveOnMiss_default (c : Core) (h : c.onMiss = Option.none) :
    effectiveOnMiss c = defaultOnMiss c.shape := by simp [effectiveOnMiss, h]

/-! ## The glyph, and the loader that inverts it -/

/-- The glyph is a **function of placement and status**, not a stored field.
This single change kills four of the six duplicate-id bugs: `--drop` cannot
turn an archive copy into a live line, because "archive copy" is not something
the glyph records. -/
def glyphAt (c : Core) (s : Site) : Glyph :=
  if c.archive = some s then Glyph.demoted
  else match c.status with
    | .settled .done    => Glyph.done
    | .settled .dropped => Glyph.dropped
    | .demoted          => Glyph.demoted
    | .live .self       => Glyph.active
    | .live .world      => Glyph.waiting
    | .live .free       => if c.archive.isSome then Glyph.demoted else Glyph.todo

/-- One observation: an id, a site, and the bytes that appear in the file. -/
structure Line where
  id   : Id
  site : Site
  text : List Char
deriving DecidableEq, Repr

def renderCore (i : Id) (c : Core) : List Line :=
  ⟨i, c.live, serializeItem i (glyphAt c c.live) c.line⟩ ::
    (match c.archive with
     | none   => []
     | some r => [⟨i, r, serializeItem i (glyphAt c r) c.line⟩])

def render (i : Id) (e : Entity) : List Line := renderCore i e.val

theorem render_le_two (i : Id) (e : Entity) : (render i e).length ≤ 2 := by
  unfold render renderCore; cases e.val.archive <;> simp

theorem render_all_same_id (i : Id) (e : Entity) : ∀ l ∈ render i e, l.id = i := by
  unfold render renderCore; cases e.val.archive <;> simp

/-- Read straight off `wf`: the archive line is in a different file. -/
theorem archive_elsewhere (e : Entity) (r : Site) (h : e.val.archive = some r) :
    r.doc ≠ e.val.live.doc := by
  have := e.property
  rw [wf_eq, h] at this
  simpa using this

/-- **The invariant that broke six times**, for one entity: one file, one
line. -/
theorem one_line_per_file (i : Id) (e : Entity) :
    ∀ l₁ ∈ render i e, ∀ l₂ ∈ render i e, l₁.site.doc = l₂.site.doc → l₁.site = l₂.site := by
  unfold render renderCore
  cases h : e.val.archive with
  | none => simp [h]
  | some r =>
      have hne := archive_elsewhere e r h
      simp only [h, List.mem_cons, List.not_mem_nil, or_false]
      rintro l₁ (rfl | rfl) l₂ (rfl | rfl) hd <;> simp_all

/-- Exactly one of the (at most two) lines is the live one — so `[-]` being
ambiguous in the file is harmless: the *role* is positional. -/
theorem exactly_one_live (i : Id) (e : Entity) :
    (render i e).countP (fun l => l.site == e.val.live) = 1 := by
  unfold render renderCore
  cases h : e.val.archive with
  | none => simp [h]
  | some r =>
      have hne := archive_elsewhere e r h
      have : ¬ (r = e.val.live) := fun hc => hne (by rw [hc])
      simp [h, this]

/-- The tombstone always renders as `[-]`, whatever the status says. -/
theorem archive_line_is_demoted (c : Core) (r : Site) (h : c.archive = some r) :
    glyphAt c r = Glyph.demoted := by simp [glyphAt, h]

/-! ## Reading a glyph back: the inverse of `glyphAt`

`glyphAt` is the only writer of a state box.  A loader therefore has exactly one
correct job — pick the state whose glyph *is* the one in the file — and getting
it wrong silently rewrites the user's file with no command run at all.  That is
what the first version of `entitiesOfDoc` did: it mapped `[-]` to `live free`
with no archive, and `glyphAt` rendered `[ ]`.

So the inverse is written down and its halves are theorems.  There are two of
them because the *live* line of a half-finished demotion is read differently
from a line standing alone:

* standing alone, every glyph has a preimage, `[-]` included — that is
  `Status.demoted`, §6.3's archive copy, and it is why a month file's
  `# Demoted` section loads;
* with an archive placement, `[ ]` has **no** preimage: while a tombstone
  stands, the live line reads `[-]`, never `[ ]`.
-/

/-- The inverse of `glyphAt` at the live site of an entity with **no** archive
placement.  Total: §6.3's `[-]` archive copy is a state, so there is no glyph a
file can carry that this refuses.  `orphanDemotion` — the loader error that
refused every `# Demoted` section in the corpus — has no source any more. -/
def statusOfGlyph : Glyph → Status
  | .todo    => .live .free
  | .active  => .live .self
  | .done    => .settled .done
  | .dropped => .settled .dropped
  | .waiting => .live .world
  | .demoted => .demoted

/-- The inverse of `glyphAt` at the live site of an entity that **does** have an
archive placement.  `[ ]` has no preimage here: while a tombstone stands, the
live line reads `[-]`. -/
def statusOfGlyphDemoted : Glyph → Option Status
  | .demoted => some (.live .free)
  | .active  => some (.live .self)
  | .done    => some (.settled .done)
  | .dropped => some (.settled .dropped)
  | .waiting => some (.live .world)
  | .todo    => none

/-- **Fidelity, unpaired.**  The entity a loader builds from a glyph renders
that same glyph back — for **every** glyph, with no side condition, which is
the part that changed: `[-]` used to have no preimage here at all. -/
theorem glyphAt_statusOfGlyph (g : Glyph) (site : Site) (l : RawItem) :
    glyphAt (coreOfLine site (statusOfGlyph g) l) site = g := by
  cases g <;> rfl

/-- **Fidelity, paired.**  Same, for the two-line form a demotion leaves: the
live site renders the glyph it was read with, and the tombstone renders `[-]`
(`archive_line_is_demoted`). -/
theorem glyphAt_statusOfGlyphDemoted {g : Glyph} {s : Status}
    (h : statusOfGlyphDemoted g = some s) (live arch : Site) (hne : arch ≠ live)
    (l : RawItem) :
    glyphAt { live := live, archive := some arch, status := s, line := l } live = g := by
  have harch : ¬ ((some arch : Option Site) = some live) := by simpa using hne
  cases g <;> simp only [statusOfGlyphDemoted, Option.some.injEq, reduceCtorEq] at h <;>
    first | (subst h; simp [glyphAt, harch]) | simp [glyphAt, harch]

/-- Whichever box is in the file, **there is a state that renders it**, and now
there is one for a `[-]` standing on its own — §4.3's month `# Demoted` record.
So "no state matches this line" is never the reason the loader rejects; it
rejects only because the *pairing* is wrong, which is a fact about the whole
plan and not about one line. -/
theorem every_glyph_has_a_state (g : Glyph) (site : Site) (l : RawItem) :
    ∃ s : Status, glyphAt (coreOfLine site s l) site = g :=
  ⟨statusOfGlyph g, glyphAt_statusOfGlyph g site l⟩

/-- **A lone `[-]` renders back as `[-]`.**  The one-line form of the theorem
above, spelled out because it is the fix: the loader used to send this glyph to
`live free` with no archive, and `glyphAt` printed `[ ]` — a document the
kernel accepted and handed back with different bytes. -/
theorem a_lone_demotion_renders_back (site : Site) (l : RawItem) :
    glyphAt (coreOfLine site .demoted l) site = Glyph.demoted := rfl

end Tm
