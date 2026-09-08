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
-/
namespace Tm

abbrev DocIx := Nat

/-- Where a line sits: which document, and its line order within it (§7.4's
rank).  There is no `horizon` field: an item's horizon **is** its file. -/
structure Site where
  doc  : DocIx
  rank : Nat
deriving DecidableEq, Repr, Inhabited

/-- §6.3's `[-]` is **not a status** — it belongs to placement.  Five states,
not six: settled (done/dropped), or live, and if live, who holds it. -/
inductive Outcome | done | dropped
deriving DecidableEq, Repr
inductive Holder | free | self | world
deriving DecidableEq, Repr
inductive Status | settled (o : Outcome) | live (h : Holder)
deriving DecidableEq, Repr

/-! ## §3.1's item, and where each of its twenty-two fields went

The first version of `Core` carried five fields.  §3.1's `Item` has
twenty-two, and the reason the entity is a **`Bool` predicate plus a
`Subtype`** rather than a record with dependent proof fields is exactly so that
this scales: widening `Core` leaves `wfPair`, `wf` and every `{c with …}` update
untouched, which `wf_ignores_the_item_fields` below states as `rfl`.

Four of the twenty-two are absent, each for a stated reason:

* `id` is the **store key**.  "An id names one item" is what `Store.get` being
  a function means, so it is not a field of the thing being named.
* `horizon` is the **file** the item sits in (`Site.doc`).  A stored horizon is
  a second answer to a question the placement already answers — S2.
* `src` is `live` plus `line`: the token vector *is* the source text, and
  `serialize_parse` says so.
* `est` and `est_original` are **views** of the token vector (`viewRemaining`,
  Line.lean).  Two stored copies of one estimate is the exact shape of the
  shipped `tm edit est=` bug, so there is one slot and a function that reads it.

Two more are **derived** rather than stored, in Plan.lean where the tree is:
`series` (§3.1: "from the `## series:<name>` section") is a fact about the
document and the rank, and `effective_shape` (§3.2) is a fact about the parent.

Everything bounded gets a `Fin` and a smart constructor, per the standing rule.
-/

/-- Minutes.  §3.1's `Dur(u32)`; `Nb` is converted through `config.block_min`
at the boundary, so nothing inside the kernel is a block and nothing is a
`Float`. -/
abbrev Dur := Nat

/-- Minutes since an epoch — §3.1's `DateTime` with the civil calendar factored
out, the same move `Grain.Day` makes one grain up.  Real ISO-week and
civil-month arithmetic is stage 5 (README gap 4). -/
abbrev Instant := Nat

/-- A time of day, in minutes since midnight.  Bounded, so it is a `Fin`:
`win:25:00-…` is not a value this kernel can hold. -/
abbrev Clock := Fin 1440

/-- The only way in, from an `HH:MM` pair. -/
def clock? (h m : Nat) : Option Clock :=
  if hh : h * 60 + m < 1440 then some ⟨_, hh⟩ else none

theorem clock_rejects_25h : clock? 25 0 = none := by decide
theorem clock_rejects_minute_60 : clock? 23 60 = none := by decide
theorem clock_accepts_2330 : (clock? 23 30).map Fin.val = some 1410 := by decide

/-- Mon = 0 … Sun = 6. -/
abbrev Weekday := Fin 7

def weekday? (n : Nat) : Option Weekday :=
  if h : n < 7 then some ⟨n, h⟩ else none

theorem weekday_rejects_7 : weekday? 7 = none := by decide

/-- §3.1's `Monthly(u8)`: a day of the month, 1–31, held zero-based. -/
abbrev MonthDay := Fin 31

def monthDay? (n : Nat) : Option MonthDay :=
  if h : 0 < n ∧ n ≤ 31 then some ⟨n - 1, by omega⟩ else none

def MonthDay.day (d : MonthDay) : Nat := d.val + 1

theorem monthDay_rejects_0  : monthDay? 0 = none := by decide
theorem monthDay_rejects_32 : monthDay? 32 = none := by decide
theorem monthDay_roundtrips (n : Nat) (h1 : 0 < n) (h2 : n ≤ 31) :
    (monthDay? n).map MonthDay.day = some n := by
  simp only [monthDay?, dif_pos (And.intro h1 h2), Option.map_some, MonthDay.day,
    Option.some.injEq]
  omega

/-- §3.1's `WindowRange`. -/
inductive WindowRange
  | daily    (fromT toT : Clock)
  | absolute (fromT toT : Instant)
deriving DecidableEq, Repr, Inhabited

/-- §3.1's `Shape`.  The four constructors are the four things the grammar's
`due:`, `at:` and `win:`+`dur:` slots can say (§4.1), and nothing else. -/
inductive Shape
  | none
  | point    (due : Instant)
  | interval (start finish : Instant)
  | window   (range : WindowRange) (dur : Dur)
deriving DecidableEq, Repr, Inhabited

/-- §3.1's calendar `Rule`. -/
inductive Rule
  | daily
  | weekdays
  | weekly      (days : List Weekday)
  | everyNDays  (n : Nat)
  | everyNWeeks (n : Nat) (d : Weekday)
  | monthly     (d : MonthDay)
deriving DecidableEq, Repr, Inhabited

/-- **Recurrence is syntax, and that is a decision, not an omission.**  A
`Recur` modelled as `Log → Instant → Option Occurrence` is not serialisable,
not `DecidableEq`, and not writable in a Markdown line — and §0 says the
Markdown is the database.  So all four of §3.1's constructors are kept as
*data*.  The denotation (§5.1's `instances`) is stage 5 and is deliberately
**not** here; nothing in this module pretends to compute an occurrence. -/
inductive Recur
  | none
  | calendar  (r : Rule)
  | afterDone (offset : Dur) (window : Option Dur)
  | onEvent   (name : List Char) (timeout : Option Dur)
deriving DecidableEq, Repr, Inhabited

/-- §3.1's `OnMiss`.  What the *default* is, is derived — see `defaultOnMiss`. -/
inductive OnMiss | expire | persist | next
deriving DecidableEq, Repr, Inhabited

/-- §3.1's `Period`, the denominator of a budget. -/
inductive Period | day | week | month
deriving DecidableEq, Repr, Inhabited

/-- §4.1's `min:6b/w`: an amount of time per period.  The amount is **minutes**
as a `Nat` — `6b` was multiplied out at the boundary. -/
structure Rate where
  amount : Dur
  per    : Period
deriving DecidableEq, Repr, Inhabited

/-- §3.1's `Budget`: a floor (`min:`), a cap (`max:`), either or both. -/
structure Budget where
  floor : Option Rate := Option.none
  cap   : Option Rate := Option.none
deriving DecidableEq, Repr, Inhabited

/-- §3.1's `Dep`: `after:^id` or `after:event:<name>` (§5.5). -/
inductive Dep
  | item  (i : Id)
  | event (name : List Char)
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
E3/E4.  The `Nodup` proof lives inside the *field's own type*, so it mentions no
other field of `Core` and `{c with …}` still works; that is the whole difference
between this and the dependent proof field the `firstprinciples` spike had to
withdraw. -/
abbrev TagSet := { l : List (List Char) // l.Nodup }

/-- The only way to build one from raw words: duplicates cannot survive. -/
def TagSet.ofList (l : List (List Char)) : TagSet := ⟨dedupTags l, dedupTags_nodup l⟩

theorem TagSet.mem_ofList (l : List (List Char)) (t : List Char) :
    t ∈ (TagSet.ofList l).val ↔ t ∈ l := dedupTags_mem l t

/-- **A duplicated tag cannot be held**, so `#lean #lean` is one tag and no
code has to remember to dedup it. -/
theorem TagSet.no_duplicates (s : TagSet) : s.val.Nodup := s.property

/-- The observable content of one entity.  `line` is the verbatim token vector
(§4.2), and `est`/`est_original` are views of it, so there is one place an
estimate can live.  The rest of §3.1's fields are here, typed. -/
structure Core where
  live      : Site
  archive   : Option Site      -- at most one tombstone a close left behind
  status    : Status
  line      : RawItem
  stamps    : List Nat         -- `demoted:` periods, newest last
  /-- §3.1 `ci: u8` — min-energy 0–5.  **`Option`, because §3.1's rule is
  "default: parent's, else 3"**: a stored 3 cannot be told from an inherited
  one, and the inheritance is derived in Plan.lean (`effectiveCi`). -/
  ci         : Option (Fin 6)     := Option.none
  /-- §3.1 `priority: Option<u8>`, explicit `!k` with k in 1–4, held
  zero-based.  §3.2's `root_priority` walks to the root for it. -/
  prio       : Option (Fin 4)     := Option.none
  /-- §3.1 `parent`.  Totality and acyclicity are **plan-level** (Plan.lean):
  they are facts about the whole store, not about one record. -/
  parent     : Option Id          := Option.none
  scope      : Scope              := .finite
  shape      : Shape              := Shape.none
  recur      : Recur              := Recur.none
  /-- The `on-miss:` **override** only.  §5.3's default is a function of the
  shape (`defaultOnMiss`), so storing a resolved value would be a second copy of
  a derived fact. -/
  onMiss     : Option OnMiss      := Option.none
  budget     : Budget             := {}
  /-- §3.1: default true; the `atomic` flag sets it false. -/
  splittable : Bool               := true
  after      : List Dep           := []
  /-- §3.1's `Loc`.  `Option Name`, not an enum with four named rooms: the
  architecture refuses to derive it because *admission* is the only query. -/
  loc        : Option (List Char) := Option.none
  /-- §4.1 `buffer:` — intervals only; blocked time before start, in minutes. -/
  buffer     : Dur                := 0
  tags       : TagSet             := ⟨[], List.nodup_nil⟩
deriving DecidableEq, Repr

/-- §3.2's `!k`, read out one-based the way the file writes it. -/
def Core.priorityK (c : Core) : Option Nat := c.prio.map (fun k => k.val + 1)

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
theorem onMiss_interval (a b : Instant) : defaultOnMiss (.interval a b) = .persist := rfl
/-- §5.3 row 2. -/
theorem onMiss_point (d : Instant) : defaultOnMiss (.point d) = .persist := rfl
/-- §5.3 rows 3 and 4 — one answer, whatever the recurrence says. -/
theorem onMiss_window (r : WindowRange) (d : Dur) : defaultOnMiss (.window r d) = .expire := rfl

/-- The value the planner uses: the `on-miss:` token if the line carries one,
otherwise §5.3's default. -/
def effectiveOnMiss (c : Core) : OnMiss := c.onMiss.getD (defaultOnMiss c.shape)

/-- §5.3 rows 5 and 6: an explicit `on-miss:` always wins. -/
theorem effectiveOnMiss_override (c : Core) (m : OnMiss) :
    effectiveOnMiss { c with onMiss := some m } = m := rfl

theorem effectiveOnMiss_default (c : Core) (h : c.onMiss = Option.none) :
    effectiveOnMiss c = defaultOnMiss c.shape := by simp [effectiveOnMiss, h]

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
setting any of §3.1's item fields therefore re-discharges *nothing*, and the
proof is `rfl`.  A record with a dependent proof field mentioning one of these
would have made every one of these updates a new obligation — the failure the
`firstprinciples` spike recorded and the architecture spike reproduced in eight
places. -/
theorem wf_ignores_the_item_fields (c : Core)
    (ci' : Option (Fin 6)) (pr : Option (Fin 4)) (pa : Option Id) (sc : Scope)
    (sh : Shape) (rc : Recur) (om : Option OnMiss) (bg : Budget) (sp : Bool)
    (af : List Dep) (lo : Option (List Char)) (bu : Dur) (tg : TagSet) :
    wf { c with ci := ci', prio := pr, parent := pa, scope := sc, shape := sh,
                recur := rc, onMiss := om, budget := bg, splittable := sp,
                after := af, loc := lo, buffer := bu, tags := tg } = wf c := rfl

/-- **The entity.**  You cannot make one without discharging `wf`. -/
def Entity := { c : Core // wf c = true }

instance : DecidableEq Entity := fun a b =>
  decidable_of_iff (a.val = b.val)
    (by constructor <;> intro h; exact Subtype.ext h; exact congrArg _ h)

/-- The glyph is a **function of placement**, not a stored field.  This single
change kills four of the six duplicate-id bugs: `--drop` cannot turn an archive
copy into a live line, because "archive copy" is not something the glyph
records. -/
def glyphAt (c : Core) (s : Site) : Glyph :=
  if c.archive = some s then Glyph.demoted
  else match c.status with
    | .settled .done    => Glyph.done
    | .settled .dropped => Glyph.dropped
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

So the inverse is written down as a partial function and its two halves are
theorems.  `none` means **the glyph is not reachable in that configuration**,
and the loader must reject rather than pick something close:

* with no archive placement, `[-]` is unreachable — a demotion is two lines;
* with an archive placement, `[ ]` is unreachable — the live line of a
  half-finished demotion is `[-]`, never `[ ]`.
-/

/-- The inverse of `glyphAt` at the live site of an entity with **no** archive
placement.  `[-]` has no preimage here: a lone `[-]` is not a state this kernel
can hold. -/
def statusOfGlyph : Glyph → Option Status
  | .todo    => some (.live .free)
  | .active  => some (.live .self)
  | .done    => some (.settled .done)
  | .dropped => some (.settled .dropped)
  | .waiting => some (.live .world)
  | .demoted => none

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
that same glyph back. -/
theorem glyphAt_statusOfGlyph {g : Glyph} {s : Status} (h : statusOfGlyph g = some s)
    (site : Site) (l : RawItem) (st : List Nat) :
    glyphAt { live := site, archive := none, status := s, line := l, stamps := st } site = g := by
  cases g <;> simp only [statusOfGlyph, Option.some.injEq, reduceCtorEq] at h <;>
    first | (subst h; rfl) | rfl

/-- **Fidelity, paired.**  Same, for the two-line form a demotion leaves: the
live site renders the glyph it was read with, and the tombstone renders `[-]`
(`archive_line_is_demoted`). -/
theorem glyphAt_statusOfGlyphDemoted {g : Glyph} {s : Status}
    (h : statusOfGlyphDemoted g = some s) (live arch : Site) (hne : arch ≠ live)
    (l : RawItem) (st : List Nat) :
    glyphAt { live := live, archive := some arch, status := s, line := l, stamps := st } live = g := by
  have harch : ¬ ((some arch : Option Site) = some live) := by simpa using hne
  cases g <;> simp only [statusOfGlyphDemoted, Option.some.injEq, reduceCtorEq] at h <;>
    first | (subst h; simp [glyphAt, harch]) | simp [glyphAt, harch]

/-- The two inverses between them cover every glyph: whichever box is in the
file, exactly one of the two configurations renders it.  So "no state matches
this line" is never the reason the loader rejects — it rejects only because the
*pairing* is wrong, which is a fact about the whole plan and not about one
line. -/
theorem every_glyph_has_a_state (g : Glyph) :
    (statusOfGlyph g).isSome = true ∨ (statusOfGlyphDemoted g).isSome = true := by
  cases g <;> simp [statusOfGlyph, statusOfGlyphDemoted]

end Tm
