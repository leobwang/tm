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
  `Core.splittable`, `Core.extra`, `Core.title`, `Core.est` and (since D6)
  `Core.parent` are functions that read it.  This is what `est` already did (§3.1's
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

**`parent` is a view too, since the owner's D6 (2026-09-13).**  It was the last
stored slot, always `none`, because reading `@O2` off a week line makes a
document set that is one file stop loading (`parentsTotal` is a load
precondition, and §6.1 lets a week item be a child of a month item) — README gap
22.  The owner chose to derive it and keep the precondition strict: `Core.parent`
is `Field.parentRef` of the line, like every other field here, a link to an id
the tree does not carry refuses the whole tree (`danglingParent`), and a cycle
refuses (`parentCycle`).  The host hands the kernel whole trees, so a week line's
`@O2` resolves against the month file it came with.  `@parent` is still an `Id`,
not §3.1's `Ref` (`@id` **or `@label`**, README gap 19): a label is read as the
id it spells, and refuses as dangling unless an item carries that id.
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

/-! ## The tombstone carries its own bytes

§6.3's week close does not write one line twice.  It marks the week line `[-]`
and **copies** it into `month/<current>#Demoted` "with `est:` = remaining and
`demoted:W37` appended", so the pair the spec's own lifecycle produces has two
lines that differ in their bytes — and §4.3's fixture pair differs in the
leading estimate (`4 6b` against `4 3b`) as well.

An entity that owned one token vector could not render both, and the loader
said so: `LErr.splitLine`, on every whole plan of the corpus that carried a
demotion.  That error was a rule about the model, not about the data.

So a tombstone is a **site and the bytes standing at it**, in one field, and
the two cannot come apart: there is no value with a placement and no text, or
text and no placement.  What this is *not* is a second copy of §3.1's fields —
those are views of `Core.line`, the record, and `the_fields_are_the_line` still
quantifies over that one vector.  The archive's bytes are a frozen
**observation** the close left in a file nobody edits again; no view reads
them, and the only thing that consumes them is `renderCore`, which writes them
back where it found them. -/
structure Tomb where
  /-- where the archive record sits -/
  site : Site
  /-- the bytes standing there, verbatim -/
  line : RawItem
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
vector** (§4.2), which is where every one of §3.1's item fields lives —
`parent` included, since D6 (the module header). -/
structure Core where
  live      : Site
  archive   : Option Tomb      -- at most one tombstone a close left behind
  status    : Status
  line      : RawItem
deriving DecidableEq, Repr

/-- Where the tombstone is, forgetting what it says.  Almost everything that
asks about the archive asks about the *placement* — `wf`, `Normalized`, the
horizon order, the section rules — and this is the projection they use. -/
def Core.archiveSite (c : Core) : Option Site := c.archive.map Tomb.site

@[simp] theorem Core.archiveSite_none {c : Core} (h : c.archive = none) :
    c.archiveSite = none := by simp [Core.archiveSite, h]

@[simp] theorem Core.archiveSite_some {c : Core} {t : Tomb} (h : c.archive = some t) :
    c.archiveSite = some t.site := by simp [Core.archiveSite, h]

/-! ## §3.1's item fields, as views of the line

One function per field, and it is the only thing that reads that field.  Each
is §4.1's view of the same bytes, so there is nothing for a second reader to
disagree with.

They read `Core.line` — the **record**, the line an id resolves to (§1.3
"writers address items by id").  §6.3 says which line that is: the copy the
close files forward, carrying `est:` = remaining and the stamp, which is also
the line `tm readopt` reopens.  The tombstone's bytes are not a second reading
of any of these fields; nothing below looks at them. -/

/-- All twenty-seven of §4.1's fields at once — the same value `renderItem`
round-trips (`field_round_trip`, Line.lean). -/
def Core.fields (c : Core) : Fields := Field.viewFields c.line

/-- §3.1 `title`: the title segment plus §4.1's unclassifiable words, which
"stay in the title". -/
def Core.title (c : Core) : List (List Char) := Field.titleWords c.line

/-! ### `parentRef` looks for an `@` before it classifies

Since D6 every plan check reads every record's parent, and `Field.parentRef`
classifies all of a line's tokens to find it.  A `.parent` kind only ever comes
from a word that begins with `@` (`kParent_classifyWord`, through the four
classifier phases), so a line with no such word has no parent and the
classification can be skipped.  `parentRef_eq_parentRefFast` is the `@[csimp]`
equality (Fast.lean's device); it sits here, ahead of `Core.parent`, because a
`csimp` lemma rewrites only the code compiled after it. -/

namespace Field

/-- A word that begins with `@`. -/
def atWord (w : List Char) : Bool := w.head? == some '@'

theorem kParent_classifyWord (w : List Char) (h : atWord w = false) :
    kParent (classifyWord w) = none := by
  unfold classifyWord
  cases hs : sigilOf w with
  | none =>
    simp only
    split
    · unfold classifyKeyed; split <;> rfl
    · unfold classifyPlain; split <;> rfl
  | some c =>
    simp only
    have hc : c ≠ '@' := by
      intro hc
      subst hc
      cases w with
      | nil => simp [sigilOf] at hs
      | cons a t =>
        have ha : a = '@' := by
          simp only [sigilOf] at hs
          split at hs
          · cases hs; rfl
          · cases hs
        subst ha
        simp [atWord] at h
    unfold classifySigil
    by_cases h1 : w.length = 1
    · rw [if_pos h1]; rfl
    · rw [if_neg h1, if_neg hc]
      by_cases h2 : c = '#'
      · rw [if_pos h2]; rfl
      · rw [if_neg h2]
        by_cases h3 : c = '!'
        · rw [if_pos h3]; unfold classifyBang; cases parsePrio w <;> rfl
        · rw [if_neg h3]; split <;> rfl

theorem findSome_kParent_phase3 : ∀ (ts : List Tok), ts.all (fun t => !atWord t.word) = true →
    (classifyPhase3 ts).findSome? kParent = none
  | [], _ => rfl
  | t :: ts, h => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    show (classifyWord t.word :: classifyPhase3 ts).findSome? kParent = none
    rw [findSome_cons_none _ _ _ (kParent_classifyWord _ h.1)]
    exact findSome_kParent_phase3 ts h.2

theorem findSome_kParent_phase2 : ∀ (ts : List Tok), ts.all (fun t => !atWord t.word) = true →
    (classifyPhase2 ts).findSome? kParent = none
  | [], _ => rfl
  | t :: ts, h => by
    show (if startsToken t.word then classifyPhase3 (t :: ts)
          else TokKind.title t.word :: classifyPhase2 ts).findSome? kParent = none
    split
    · exact findSome_kParent_phase3 (t :: ts) h
    · simp only [List.all_cons, Bool.and_eq_true] at h
      rw [findSome_cons_none _ _ _ rfl]
      exact findSome_kParent_phase2 ts h.2

theorem findSome_kParent_phase1 (ts : List Tok) (h : ts.all (fun t => !atWord t.word) = true) :
    (classifyPhase1 ts).findSome? kParent = none := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    show (match estSlot t.word with
          | some d => TokKind.est d :: classifyPhase2 ts
          | none   => classifyPhase2 (t :: ts)).findSome? kParent = none
    split
    · simp only [List.all_cons, Bool.and_eq_true] at h
      rw [findSome_cons_none _ _ _ rfl]
      exact findSome_kParent_phase2 ts h.2
    · exact findSome_kParent_phase2 (t :: ts) h

/-- **A line with no `@` word has no parent.** -/
theorem findSome_kParent_phase0 (ts : List Tok) (h : ts.all (fun t => !atWord t.word) = true) :
    (classifyPhase0 ts).findSome? kParent = none := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    show (match ciSlot t.word with
          | some c => TokKind.ci c :: classifyPhase1 ts
          | none   => classifyPhase1 (t :: ts)).findSome? kParent = none
    split
    · simp only [List.all_cons, Bool.and_eq_true] at h
      rw [findSome_cons_none _ _ _ rfl]
      exact findSome_kParent_phase1 ts h.2
    · exact findSome_kParent_phase1 (t :: ts) h

theorem parentRef_of_no_at (r : RawItem) (h : r.toks.all (fun t => !atWord t.word) = true) :
    parentRef r = none := by
  unfold parentRef kinds
  cases hb : r.boxed with
  | true  => simp only [if_pos]; exact findSome_kParent_phase0 r.toks h
  | false => simp only [Bool.false_eq_true, if_false]; exact findSome_kParent_phase2 r.toks h

/-- `parentRef`, classifying only a line that has an `@` word. -/
def parentRefFast (r : RawItem) : Option (List Char) :=
  if r.toks.all (fun t => !atWord t.word) then none else (kinds r).findSome? kParent

@[csimp] theorem parentRef_eq_parentRefFast : @parentRef = @parentRefFast := by
  funext r
  unfold parentRefFast
  split
  · rename_i h; exact parentRef_of_no_at r h
  · rfl

end Field

/-- §3.1 `parent`: the line's `@parent` token (§4.1), read by the one reader
`Field.parentRef`.  A view, not a slot (the owner's D6, 2026-09-13; README gap
22): a stored parent could disagree with the `@O2` the file carries, and before
D6 it did — it was `none` on every record while the line said `@O2`.  Totality
and acyclicity are **plan-level** (Plan.lean's `parentsTotal`,
`parentsAcyclic`): they are facts about the whole store, not about one record. -/
def Core.parent (c : Core) : Option Id := Field.parentRef c.line

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

/-- §3.1 `pref:`: the anchor inside a window instance's range (§8.2 step 2, fork
`Item::pref`).  Added at stage 6 step P2 — the planner is its first reader, and §3.1's rule is
that one function reads one field, so it is declared **here** beside the other twenty-six
rather than in `Planner.lean`. -/
def Core.pref (c : Core) : Option Field.Pref := Field.viewPref c.line

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
      c.extra = d.extra ∧ c.est = d.est ∧ c.parent = d.parent := by
  obtain ⟨_, _, _, ln⟩ := c
  obtain ⟨_, _, _, ln'⟩ := d
  have hl : ln = ln' := h
  subst hl
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩

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
/-- The loader's record carries the `@parent` its line carries — the view the
plan-level `parentsTotal` and `parentsAcyclic` read (D6).  Before D6 the right
side was `none` whatever the line said. -/
theorem coreOfLine_parent (site : Site) (st : Status) (r : RawItem) :
    (coreOfLine site st r).parent = Field.parentRef r := rfl

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

def wf (c : Core) : Bool := wfPair c.live c.archiveSite

@[simp] theorem wf_eq (c : Core) : wf c = wfPair c.live c.archiveSite := rfl

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
theorem wf_ignores_the_item_fields (c : Core) (l : RawItem) :
    wf { c with line := l } = wf c := rfl

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

/-- The box a status puts in a file.  Six states, six glyphs, and it is a
bijection — `statusOfGlyph` below is its inverse both ways round. -/
def glyphOfStatus : Status → Glyph
  | .settled .done    => Glyph.done
  | .settled .dropped => Glyph.dropped
  | .demoted          => Glyph.demoted
  | .live .self       => Glyph.active
  | .live .world      => Glyph.waiting
  | .live .free       => Glyph.todo

/-- The glyph is a **function of placement and status**, not a stored field.
This single change kills four of the six duplicate-id bugs: `--drop` cannot
turn an archive copy into a live line, because "archive copy" is not something
the glyph records.

The tombstone's box is `[-]` because it is a tombstone — that is what a line in
`month/…# Demoted` *is*.  The record's box is its status, **and nothing else**:
the previous version also forced `[-]` on a `live free` record whenever a
tombstone stood, on the reading that "a demotion writes `[-]` at both sites".
That reading is §6.3's *post-close* snapshot only.  `tm readopt` turns the
record back to `[ ]` and the archive stands (§6.3: "`[-]` → `[ ]`, stamp
kept"), which is the shape §4.3's own fixture ships — a `[ ]` in
`week/2026-W37.md` beside the `[-]` in `month/2026-09.md # Demoted`.  Forcing
the box made that pair unreadable and made `[ ]` a glyph with no preimage. -/
def glyphAt (c : Core) (s : Site) : Glyph :=
  if c.archiveSite = some s then Glyph.demoted else glyphOfStatus c.status

/-- At the live site the box is the status, whatever the archive is doing. -/
theorem glyphAt_live (c : Core) (h : wf c = true) :
    glyphAt c c.live = glyphOfStatus c.status := by
  have : c.archiveSite ≠ some c.live := by
    cases ha : c.archiveSite with
    | none => simp
    | some r =>
        simp only [wf_eq, ha, wfPair_some, bne_iff_ne, ne_eq] at h
        intro hc
        exact h (congrArg Site.doc (Option.some.inj hc))
  simp [glyphAt, this]

/-- One observation: an id, a site, and the bytes that appear in the file. -/
structure Line where
  id   : Id
  site : Site
  text : List Char
deriving DecidableEq, Repr

/-- The lines an entity denotes: the record at its live placement, and — when a
close left one — the tombstone at its own placement, in **its own bytes**.
Rendering both sites from one token vector is what could not reproduce §6.3's
pair; the archive's text is the text the close froze there. -/
def renderCore (i : Id) (c : Core) : List Line :=
  ⟨i, c.live, serializeItem i (glyphAt c c.live) c.line⟩ ::
    (match c.archive with
     | none   => []
     | some t => [⟨i, t.site, serializeItem i (glyphAt c t.site) t.line⟩])

def render (i : Id) (e : Entity) : List Line := renderCore i e.val

theorem render_le_two (i : Id) (e : Entity) : (render i e).length ≤ 2 := by
  unfold render renderCore; cases e.val.archive <;> simp

theorem render_all_same_id (i : Id) (e : Entity) : ∀ l ∈ render i e, l.id = i := by
  unfold render renderCore; cases e.val.archive <;> simp

/-- Read straight off `wf`: the archive line is in a different file. -/
theorem archive_elsewhere (e : Entity) (r : Site) (h : e.val.archiveSite = some r) :
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
  | some t =>
      have hne := archive_elsewhere e t.site (Core.archiveSite_some h)
      simp only [h, List.mem_cons, List.not_mem_nil, or_false]
      rintro l₁ (rfl | rfl) l₂ (rfl | rfl) hd <;> simp_all

/-- Exactly one of the (at most two) lines is the live one — so `[-]` being
ambiguous in the file is harmless: the *role* is positional. -/
theorem exactly_one_live (i : Id) (e : Entity) :
    (render i e).countP (fun l => l.site == e.val.live) = 1 := by
  unfold render renderCore
  cases h : e.val.archive with
  | none => simp [h]
  | some t =>
      have hne := archive_elsewhere e t.site (Core.archiveSite_some h)
      have : ¬ (t.site = e.val.live) := fun hc => hne (by rw [hc])
      simp [h, this]

/-- The tombstone always renders as `[-]`, whatever the status says. -/
theorem archive_line_is_demoted (c : Core) (r : Site) (h : c.archiveSite = some r) :
    glyphAt c r = Glyph.demoted := by simp [glyphAt, h]

/-! ## Reading a glyph back: the inverse of `glyphAt`

`glyphAt` is the only writer of a state box.  A loader therefore has exactly one
correct job — pick the state whose glyph *is* the one in the file — and getting
it wrong silently rewrites the user's file with no command run at all.  That is
what the first version of `entitiesOfDoc` did: it mapped `[-]` to `live free`
with no archive, and `glyphAt` rendered `[ ]`.

So the inverse is written down and it is one function, not two.  The previous
version had a second, *partial* inverse for the live line of a pair, on the
reading that "a demotion writes `[-]` at both sites, so `[ ]` has no preimage
while a tombstone stands".  §6.3 refutes it in one sentence: `tm readopt` is
"`[-]` → `[ ]`, stamp kept", and what it reopens is the record, so a `[ ]`
record beside a standing `[-]` archive is a shape the lifecycle produces —
§4.3's own fixture pair.  With the box no longer forced at the live site the
inverse is `statusOfGlyph`, total, paired or not, and the six-way
`Status ≃ Glyph` correspondence is a bijection with no side conditions. -/

/-- The inverse of `glyphOfStatus`, and so of `glyphAt` at a live site.
Total: §6.3's `[-]` archive copy is a state, so there is no glyph a file can
carry that this refuses.  `orphanDemotion` — the loader error that refused
every `# Demoted` section in the corpus — has no source any more. -/
def statusOfGlyph : Glyph → Status
  | .todo    => .live .free
  | .active  => .live .self
  | .done    => .settled .done
  | .dropped => .settled .dropped
  | .waiting => .live .world
  | .demoted => .demoted

/-- **The box determines the state.** -/
theorem glyphOfStatus_statusOfGlyph (g : Glyph) : glyphOfStatus (statusOfGlyph g) = g := by
  cases g <;> rfl

/-- **And the state determines the box** — so nothing is collapsed on the way
in, and a loader cannot read two different files into one status. -/
theorem statusOfGlyph_glyphOfStatus (s : Status) : statusOfGlyph (glyphOfStatus s) = s := by
  match s with
  | .settled .done | .settled .dropped | .demoted
  | .live .self | .live .world | .live .free => rfl

/-- **Fidelity, unpaired.**  The entity a loader builds from a glyph renders
that same glyph back — for **every** glyph, with no side condition, which is
the part that changed: `[-]` used to have no preimage here at all. -/
theorem glyphAt_statusOfGlyph (g : Glyph) (site : Site) (l : RawItem) :
    glyphAt (coreOfLine site (statusOfGlyph g) l) site = g := by
  cases g <;> rfl

/-- **Fidelity, paired**, and now with no side condition on the glyph.  For the
two-line form §6.3 leaves: the record renders the box it was read with —
`[ ]` included, which is the case the partial inverse could not express — and
the tombstone renders `[-]` (`archive_line_is_demoted`) in its **own** bytes.

This is the theorem `statusOfGlyphDemoted` used to state for five of the six
glyphs; the sixth was not an exclusion the spec asked for. -/
theorem glyphAt_statusOfGlyph_paired (g : Glyph) (live arch : Site) (hne : arch ≠ live)
    (l a : RawItem) :
    glyphAt { live := live, archive := some ⟨arch, a⟩, status := statusOfGlyph g, line := l }
        live = g := by
  have harch : ¬ ((some arch : Option Site) = some live) := by simpa using hne
  cases g <;> simp [glyphAt, Core.archiveSite, harch, glyphOfStatus, statusOfGlyph]

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

/-- **A demotion pair whose two lines differ in their bytes renders both of
them.**  §6.3's week close writes the record with `est:` = remaining and a
`demoted:` stamp and leaves the week line as it stood, so `l ≠ a` is the
*normal* case and not a corner.  The entity that owns one token vector renders
`serializeItem i g l` twice; this one renders the record's bytes at the record
and the archive's bytes at the archive, which is what the corpus's whole plans
need and what `LErr.splitLine` used to refuse.

Both hypotheses are load-bearing: `hne` is `wf`, and without it the two lines
are one file's and `one_line_per_file` is false. -/
theorem a_differing_demotion_pair_renders_back (i : Id) (g : Glyph) (live arch : Site)
    (hne : arch ≠ live) (l a : RawItem) :
    renderCore i { live := live, archive := some ⟨arch, a⟩, status := statusOfGlyph g,
                   line := l }
      = [⟨i, live, serializeItem i g l⟩, ⟨i, arch, serializeItem i Glyph.demoted a⟩] := by
  have harch : ¬ ((some arch : Option Site) = some live) := by simpa using hne
  unfold renderCore
  rw [glyphAt_statusOfGlyph_paired g live arch hne l a]
  simp [glyphAt, Core.archiveSite]

end Tm
