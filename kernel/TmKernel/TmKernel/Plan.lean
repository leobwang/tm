import TmKernel.Grain
import TmKernel.State
/-!
# The plan is one object

The whole collection — every month, week and day file, backlog, routines,
optional, calendar — is a single value, and every command is one transformation
on it.

Two design decisions carry the invariant:

1. **The store is a partial function `Id → Option Entity`.**  "An id names one
   item" is therefore not an invariant to maintain — it is what "function"
   means.  There is no `record_rank`, no `is_real_duplicate`, no `choose`
   tie-break, and no `drop_stale_demotion` repair, because there is nothing
   for them to repair.
2. **A document holds prose only.**  Headings, blank lines, comments and
   generated blocks are `prose` entries carrying their exact bytes and their
   rank.  Item lines are *absent* from `Doc` entirely: they are rendered from
   the entity that owns them.

The consequence is `no_two_lines_of_one_id_in_one_file` below — a theorem about
*every* `PlanCore`, so no command has to preserve it and no command can break
it, including commands nobody has written yet.
-/
namespace Tm

/-! §4.1's value types — the same ones `State.lean` opens.  There is one
`Shape` in this kernel and this is it. -/

open Field (Shape Recur Rule Rate Period OnMiss Dep WindowRange Loc Stamp Dur DT Moment)

/-- The entity store.  `dom` is an enumeration order and nothing more;
`Std.HashMap` instantiates this interface, and keeping the proofs behind it is
the answer to the FFI spike's "a fast checker and a provable checker may be two
artifacts". -/
structure Store where
  get      : Id → Option Entity
  dom      : List Id
  domSpec  : ∀ i, i ∈ dom ↔ (get i).isSome = true
  domNodup : dom.Nodup

/-- Replace the entity at an id that already exists.  The domain is unchanged,
so both store obligations are discharged here once, not at each call site. -/
def Store.set (s : Store) (i : Id) (e : Entity) (h : (s.get i).isSome = true) : Store where
  get := fun j => if j = i then some e else s.get j
  dom := s.dom
  domSpec := by
    intro j
    by_cases hj : j = i
    · subst hj
      constructor
      · intro _; simp
      · intro _; exact (s.domSpec j).mpr h
    · simp only [hj, if_false]
      exact s.domSpec j
  domNodup := s.domNodup

@[simp] theorem Store.get_set_self (s : Store) (i : Id) (e : Entity) (h) :
    (s.set i e h).get i = some e := by simp [Store.set]

@[simp] theorem Store.get_set_other (s : Store) (i j : Id) (e : Entity) (h) (hj : j ≠ i) :
    (s.set i e h).get j = s.get j := by simp [Store.set, hj]

@[simp] theorem Store.dom_set (s : Store) (i : Id) (e : Entity) (h) :
    (s.set i e h).dom = s.dom := rfl

/-- A document body: **prose only**.  Item lines are holes filled by `render`,
which is why `move` has no `append` to be missing a precondition on.

`region` is the horizon block the file *is* — `week/2026-W37.md` is `⟨week, 35⟩`
— and `none` is backlog, the **absence** of a bound rather than a coarser
grain.  It is not decoration: it is what says which of a demotion's two lines is
the tombstone (`demotionsOriented` below), and without it that question has no
answer in the files. -/
structure Doc where
  path   : List Char
  prose  : List (Nat × List Char)
  region : Option Region
deriving Repr, Inhabited

structure PlanCore where
  docs  : List Doc
  store : Store

/-- Every line the plan denotes.  A fold over the store, so each id is visited
once and each entity renders at most twice. -/
def PlanCore.lines (p : PlanCore) : List Line :=
  p.store.dom.flatMap (fun i =>
    match p.store.get i with
    | none   => []
    | some e => render i e)

/-! ## The invariant, as a theorem about the type -/

/-- **The sentence six code paths violated**, proved once for every possible
plan: two lines carrying one id in one file are the same line.  Nothing in the
proof mentions a command, so nothing a command does can break it. -/
theorem no_two_lines_of_one_id_in_one_file (p : PlanCore)
    (l₁ l₂ : Line) (h₁ : l₁ ∈ p.lines) (h₂ : l₂ ∈ p.lines)
    (hid : l₁.id = l₂.id) (hdoc : l₁.site.doc = l₂.site.doc) : l₁.site = l₂.site := by
  unfold PlanCore.lines at h₁ h₂
  simp only [List.mem_flatMap] at h₁ h₂
  obtain ⟨i₁, _, hl₁⟩ := h₁
  obtain ⟨i₂, _, hl₂⟩ := h₂
  cases g₁ : p.store.get i₁ with
  | none => rw [g₁] at hl₁; simp at hl₁
  | some e₁ =>
    cases g₂ : p.store.get i₂ with
    | none => rw [g₂] at hl₂; simp at hl₂
    | some e₂ =>
      rw [g₁] at hl₁; rw [g₂] at hl₂
      have e1 : l₁.id = i₁ := render_all_same_id i₁ e₁ l₁ hl₁
      have e2 : l₂.id = i₂ := render_all_same_id i₂ e₂ l₂ hl₂
      have hk : i₁ = i₂ := by rw [← e1, ← e2, hid]
      subst hk
      have : e₁ = e₂ := by rw [g₁] at g₂; exact (Option.some.injEq _ _ ▸ g₂.symm) ▸ rfl
      subst this
      exact one_line_per_file i₁ e₁ l₁ hl₁ l₂ hl₂ hdoc

theorem filter_flatMap {α β} (l : List α) (f : α → List β) (p : β → Bool) :
    (l.flatMap f).filter p = l.flatMap (fun a => (f a).filter p) := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.filter_append, ih]

theorem render_filter_other (i j : Id) (e : Entity) (h : ¬ (i = j)) :
    (render i e).filter (fun l => l.id == j) = [] := by
  unfold render renderCore
  cases e.val.archive <;> simp [h]

theorem render_filter_self (i : Id) (e : Entity) :
    (render i e).filter (fun l => l.id == i) = render i e := by
  unfold render renderCore
  cases e.val.archive <;> simp

theorem flatMap_of_all_empty (t : List Id) (f : Id → List Line) (h : ∀ j ∈ t, f j = []) :
    t.flatMap f = [] := by
  induction t with
  | nil => simp
  | cons b s ih => simp [h b (by simp), ih (fun j hj => h j (by simp [hj]))]

theorem sum_over_nodup_one_key (dom : List Id) (i : Id) (f : Id → List Line)
    (hz : ∀ j ∈ dom, j ≠ i → f j = []) (hn : dom.Nodup) (hb : (f i).length ≤ 2) :
    (dom.flatMap f).length ≤ 2 := by
  induction dom with
  | nil => simp
  | cons a t ih =>
      simp only [List.flatMap_cons, List.length_append, List.nodup_cons] at *
      by_cases hai : a = i
      · subst hai
        have hall : ∀ j ∈ t, f j = [] :=
          fun j hj => hz j (by simp [hj]) (by rintro rfl; exact hn.1 hj)
        rw [flatMap_of_all_empty t f hall]
        simpa using hb
      · rw [hz a (by simp) hai]
        have := ih (fun j hj => hz j (by simp [hj])) hn.2
        simpa using this

/-- **How many lines one id can produce over the whole plan: two.**  The
archive copy is the only second line, and it is in a different file. -/
theorem lines_per_id_le_two (p : PlanCore) (i : Id) :
    ((p.lines).filter (fun l => l.id == i)).length ≤ 2 := by
  unfold PlanCore.lines
  rw [filter_flatMap]
  refine sum_over_nodup_one_key p.store.dom i _ ?_ p.store.domNodup ?_
  · intro j _ hji
    cases g : p.store.get j with
    | none => simp [g]
    | some ej => simp only [g]; exact render_filter_other j i ej hji
  · cases g : p.store.get i with
    | none => simp [g]
    | some ei => simp only [g]; rw [render_filter_self i ei]; exact render_le_two i ei

/-! ## The plan-level tier: a document holds no item lines

`Doc.prose` is verbatim text, so nothing in its *type* stops a writer putting
an item line there — which would be `move_to`'s append wearing a disguise.
That obligation lives in the third tier of the design: one decidable checker
over the whole value, discharged once at the boundary.

`planWf` is exactly what `tm check` runs, so the checker cannot be weaker than
the invariant — the class of bug where three `^m2` lines across two month files
pass `tm check` at exit 0. -/

def docWf (d : Doc) : Bool := d.prose.all (fun q => !isItemLine q.2)

def docsWf (p : PlanCore) : Bool := p.docs.all docWf

/-! ### The second plan-level obligation: a placement names a file that exists

`Site.doc` is a `Nat` and `renderDocAt` renders the indices that exist, so a
placement pointing past the end of `docs` does not raise anything — the line
simply is not emitted, and the item is **gone** with the kernel reporting `ok`.
That is the same shape of missing precondition as `move_to`'s, moved from
"the destination already holds this id" to "the destination is not a file", and
it is exactly as fatal.

So it joins the decidable plan-level checker, and `no_line_is_lost` below turns
it into the sentence that matters: every line a plan denotes lands in a document
that exists.  A command reaches the destination only through `Dest` (Cmd.lean),
which carries the proof, so the out-of-range case cannot be written either. -/

def siteInRange (p : PlanCore) (s : Site) : Bool := s.doc < p.docs.length

def entityInRange (p : PlanCore) (e : Entity) : Bool :=
  siteInRange p e.val.live &&
    (match e.val.archiveSite with
     | none   => true
     | some r => siteInRange p r)

def sitesInRange (p : PlanCore) : Bool :=
  p.store.dom.all (fun i =>
    match p.store.get i with
    | none   => true
    | some e => entityInRange p e)

/-! ### The third: two documents may not share a path

`Site.doc` is a **list index**, so a theorem quantified over `Site.doc` says
"one index, one line" — which is not the sentence anyone cares about.  What
reaches the disk is a *path*, and two documents at different indices carrying
one path put two lines of one id into one file while every index-level theorem
stays true.  Path injectivity is therefore part of what it means to be a plan,
and `no_two_lines_of_one_id_in_one_file` is restated over paths below. -/

def pathsDistinct (p : PlanCore) : Bool := decide ((p.docs.map Doc.path).Nodup)

/-! ### The fourth: where the boxes tie, the files must not

**Which line of a demotion pair is the tombstone, and how the kernel decides.**
Two answers are available and §6.3 supplies both, so the question is which one
governs when they disagree.

* **The box.** §6.3's archive record is written `[-]` and stays `[-]`: the week
  close marks the week line `[-]` and files a `[-]` copy into
  `month/<current>#Demoted`, and the only thing that reopens a box is
  `tm readopt`, which reopens *the record*.  So a line that is not `[-]` is
  never an archive copy.
* **The files.** The record goes to `closeTo`, which is strictly after the
  region that was closed (`demotion_target_follows_the_closed_region`, Grain).

They agree everywhere they both speak, and each is silent where the other is
not.  The box is silent immediately after a close, when both lines read `[-]`.
The files are silent — and worse, *wrong* — after `tm readopt ^id --to week`
("`[-]` → `[ ]`, stamp kept"), which leaves the reopened record in a **week**
and the standing archive in a **month**: §4.3's own fixture pair, and the shape
`check_fixtures.rs` asserts has zero problems.  There the file order says the
week line is the tombstone and the week line reads `[ ]`.

So the rule is lexicographic — **box first, files second** — and §3.1 is why
that order and not the other: `state` is a *stored* field of an item and
`horizon` is "derived from file path".  A derived fact may break a tie the
stored one leaves; it may not overrule it.  (This is the shape of `tree.rs`'s
`record_rank` too, which ranks `is_archive_copy` ahead of everything else; the
kernel reaches it from §6.3 rather than from the Rust, and uses the horizon
where the Rust uses the stamp count.  The two tie-breaks agree on every pair
§6.3 writes, because the close appends `demoted:` to the copy it files forward
and to nothing else.)

The consequence for this conjunct: the horizon obligation applies **exactly
when the boxes tie**, which is when the record's own status is `demoted`.  The
previous version demanded it unconditionally, and that is what refused every
whole plan in the corpus that carried §4.3's pair.  It is still a real check —
`demote` writes a `[-]` record, so every demotion a close performs has to
discharge it — and it is still what stops the kernel writing a pair the loader
would then have to guess at (`mapAt_rejects_unoriented`,
`demote_into_a_horizon_that_does_not_follow_is_rejected`).  What it no longer
does is refuse the readopted pair, which no reader ever had trouble with. -/

def docRegion (p : PlanCore) (k : DocIx) : Option Region :=
  match p.docs[k]? with
  | none   => none
  | some d => d.region

def demotionOriented (p : PlanCore) (e : Entity) : Bool :=
  match e.val.archive with
  | none   => true
  | some t =>
    if glyphOfStatus e.val.status = Glyph.demoted then
      horizonPrecedes (docRegion p t.site.doc) (docRegion p e.val.live.doc)
    else true

def demotionsOriented (p : PlanCore) : Bool :=
  p.store.dom.all (fun i =>
    match p.store.get i with
    | none   => true
    | some e => demotionOriented p e)

/-! ### The conjunct still bites, and the weakening is real

Two decided witnesses over one plan — a week file and a month file, one entity
whose tombstone is in the **month** and whose record is in the **week**, which
is backwards for the horizon order and is §4.3's own shape.

They are here rather than in a test because they are the two halves of the
change and each is the thing a later simplification would break: relax the
conjunct to `true` and the first fails; restore the unconditional horizon
demand and the second fails. -/

private def orientDocs : List Doc :=
  [⟨['w'], [], some ⟨week, 35⟩⟩, ⟨['m'], [], some ⟨month, 8⟩⟩]

private def orientCore (st : Status) : Core :=
  { live := ⟨0, 0⟩, archive := some ⟨⟨1, 0⟩, ⟨[], []⟩⟩, status := st, line := ⟨[], []⟩ }

private def orientPlan (st : Status) : PlanCore :=
  ⟨orientDocs,
   { get := fun j => if j = ['m','2'] then some ⟨orientCore st, rfl⟩ else none
     dom := [['m','2']]
     domSpec := by intro j; by_cases h : j = ['m','2'] <;> simp [h, Option.isSome]
     domNodup := by simp }⟩

/-- **It bites.**  A record that still reads `[-]` with its tombstone in a
later horizon is not a plan: the loader could not tell the two lines apart, so
`planWf` refuses it and `mapAt` refuses to produce it. -/
theorem a_backwards_demotion_is_refused : demotionsOriented (orientPlan .demoted) = false := by
  decide

/-- **And the weakening is real, not a hole.**  Reopen the record — §6.3's
`readopt`, "`[-]` → `[ ]`, stamp kept" — and the same two placements are a
plan, because the boxes now say which line is which and no file has to.  This
is the pair §4.3 ships and the one the unconditional rule refused. -/
theorem a_reopened_record_needs_no_horizon :
    demotionsOriented (orientPlan (.live .free)) = true := by decide

/-! ### The rest of the plan-level tier: §3.1's item fields

`Core` now carries §3.1's twenty-two fields, and five of them — `parent`,
`after`, `shape`, `scope`, `recur` — mean nothing until the *whole* plan is
consulted.  "`@m1` names an item" and "`after:^t4` does not wait on itself" are
not facts about a record; they are facts about the store, exactly like
"`Site.doc` names a file that exists".

So they go where the architecture's third tier says: **one decidable checker
over the whole value**, joined into `planWf`, re-established by computation on
every post-state (`WfPlan.mapAt`).  That is what makes them unforgettable, and
it is why the answer to "cycles are a `tm check` error" (§5.5) is that a cyclic
plan is not a value of this type.

Acyclicity over a finite domain is the substance here, and it is done twice
because the two relations have different shapes:

* `parent` is a **partial function**, so its acyclicity is a bounded walk:
  climb `|dom| + 1` links and you must have fallen off the top.  The bound is
  enough by pigeonhole — the domain is finite and `Nodup`
  (`parentsAcyclic_complete`), and the check is not merely conservative
  (`parentsAcyclic_sound`).
* `after` is a **relation**, so its acyclicity is a peel: strike out every id
  that no longer waits on anything still standing, `|dom|` times.  Nothing left
  standing means no *deadlocked* set — a non-empty set in which every id waits
  on another id of the set, which is the standard finite characterisation of
  "contains a cycle".  Both directions are proved and neither needs pigeonhole
  (`afterAcyclic_sound`, `afterAcyclic_complete`).
-/

/-- `pre` is a prefix of `s`. -/
def hasPrefix : List Char → List Char → Bool
  | [],      _       => true
  | _ :: _,  []      => false
  | a :: as, b :: bs => a == b && hasPrefix as bs

/-- §2's repository layout, as the only thing that says what kind of file a
document is.  `Doc.region` cannot: `calendar/2026-W37.md` and
`week/2026-W37.md` are the same region, and backlog, routines and optional all
have none. -/
inductive DocKind | month | week | day | calendar | routines | optional | backlog | other
deriving DecidableEq, Repr, Inhabited

def docKind (d : Doc) : DocKind :=
  if hasPrefix "month/".toList d.path then .month
  else if hasPrefix "week/".toList d.path then .week
  else if hasPrefix "day/".toList d.path then .day
  else if hasPrefix "calendar/".toList d.path then .calendar
  else if d.path == "routines.md".toList then .routines
  else if d.path == "optional.md".toList then .optional
  else if d.path == "backlog.md".toList then .backlog
  else .other

def docKindAt (p : PlanCore) (k : DocIx) : DocKind :=
  match p.docs[k]? with
  | none   => .other
  | some d => docKind d

/-! #### §4.2's sections, derived from the prose and the rank

An item's section is **not a field**.  It is the last heading line at or before
the item's rank, which is a fact about the document the item sits in — so it
cannot disagree with the file, and a command that moves a line changes its
section for free. -/

def isHeading (cs : List Char) : Bool := cs.head? == some '#'

/-- The text of a heading with its `#`s and leading spaces stripped, so
`# Demoted` and `## Demoted` are one name. -/
def headingBody (cs : List Char) : List Char :=
  (cs.dropWhile (fun c => c == '#')).dropWhile isSp

/-- §4.2: exactly three heading names mean anything. -/
inductive SecKind | demoted | pinned | series (name : List Char) | organisational
deriving DecidableEq, Repr, Inhabited

def secKind (cs : List Char) : SecKind :=
  let b := headingBody cs
  if b == "Demoted".toList then .demoted
  else if b == "Pinned".toList then .pinned
  else if hasPrefix "series:".toList b then .series (b.drop 7)
  else .organisational

/-- The heading with the greatest rank strictly below `rank`. -/
def lastHeadingBefore (d : Doc) (rank : Nat) : Option (Nat × List Char) :=
  d.prose.foldl (fun acc q =>
    if isHeading q.2 && decide (q.1 < rank) then
      match acc with
      | none   => some q
      | some b => if b.1 < q.1 then some q else some b
    else acc) none

/-- The section a placement sits in.  `none` means the file has no heading
above it at all. -/
def sectionAt (p : PlanCore) (s : Site) : Option (List Char) :=
  match p.docs[s.doc]? with
  | none   => none
  | some d => (lastHeadingBefore d s.rank).map Prod.snd

def sectionKindAt (p : PlanCore) (s : Site) : Option SecKind :=
  (sectionAt p s).map secKind

/-- §3.1's `series: Option<(String, u32)>`, **derived**: the name is the
section's.  (§5.4's *head* — the first member that is not done or dropped — is
a planner concept and is not here; see the README's gap list.) -/
def seriesOf (p : PlanCore) (s : Site) : Option (List Char) :=
  match sectionKindAt p s with
  | some (.series n) => some n
  | _                => none

/-! #### `Normalized`: a rank names one line

Ranks are §7.4's tie-break and `weave`'s ordering key, so two lines of one
document sharing a rank is an ordering the file does not determine.  It is a
plan-level predicate and not a per-entity obligation, because a collision is an
ambiguity between *two* entities and neither of them is malformed. -/

/-- Every rank a document uses — its prose lines and the item lines its
entities render, together, because `weave` orders them against each other. -/
def docRanks (p : PlanCore) (k : DocIx) : List Nat :=
  (match p.docs[k]? with
   | none   => []
   | some d => d.prose.map Prod.fst) ++
  ((p.lines.filter (fun l => l.site.doc == k)).map (fun l => l.site.rank))

def normalized (p : PlanCore) : Bool :=
  (List.range p.docs.length).all (fun k => decide (docRanks p k).Nodup)

/-! #### `@parent`: total, and acyclic -/

/-- One link up.  `none` both for "no parent" and for "a parent that is not an
item of this plan" — `parentsTotal` is what separates them. -/
def parentStep (p : PlanCore) (i : Id) : Option Id :=
  match p.store.get i with
  | none   => none
  | some e => e.val.parent

/-- The `n`-th ancestor of `i`, or `none` if the chain is shorter than `n`. -/
def anc (p : PlanCore) : Nat → Id → Option Id
  | 0,     i => some i
  | n + 1, i => match parentStep p i with
                | none   => none
                | some j => anc p n j

/-- Climb at most `n` links, stopping where the chain does. -/
def climb (p : PlanCore) : Nat → Id → Id
  | 0,     i => i
  | n + 1, i => match parentStep p i with
                | none   => i
                | some j => climb p n j

/-- One more than the number of ids there are: a chain this long has visited
some id twice. -/
def fuel (p : PlanCore) : Nat := p.store.dom.length + 1

def parentsTotal (p : PlanCore) : Bool :=
  p.store.dom.all (fun i =>
    match parentStep p i with
    | none   => true
    | some j => (p.store.get j).isSome)

def parentsAcyclic (p : PlanCore) : Bool :=
  p.store.dom.all (fun i => (anc p (fuel p) i).isNone)

/-- §3.2's `root(item)`.  Total by construction; `rootOf_is_a_root` is what
says the fuel was not merely exhausted. -/
def rootOf (p : PlanCore) (i : Id) : Id := climb p (fuel p) i

/-- `i` is its own proper ancestor — §5.5's error, for the parent relation. -/
def OnACycle (p : PlanCore) (i : Id) : Prop := ∃ n, 0 < n ∧ anc p n i = some i

/-! #### `after:`: total, and acyclic -/

def depIds (ds : List Dep) : List Id :=
  ds.filterMap (fun d => match d with | .item i => some i | .event _ => none)

def depsOf (p : PlanCore) (i : Id) : List Id :=
  match p.store.get i with
  | none   => []
  | some e => depIds e.val.after

def afterTotal (p : PlanCore) : Bool :=
  p.store.dom.all (fun i => (depsOf p i).all (fun j => (p.store.get j).isSome))

/-- One round: keep only the ids that still wait on something inside `rest`.
Everything struck out is an id whose dependencies are all already settled or
outside the set, i.e. one that could be scheduled next. -/
def peel (p : PlanCore) (rest : List Id) : List Id :=
  rest.filter (fun i => (depsOf p i).any (fun j => decide (j ∈ rest)))

def peelN (p : PlanCore) : Nat → List Id → List Id
  | 0,     r => r
  | n + 1, r => peelN p n (peel p r)

def afterAcyclic (p : PlanCore) : Bool :=
  (peelN p p.store.dom.length p.store.dom).isEmpty

/-- **§5.5's cycle, as the characterisation that is decidable on a finite
domain**: a non-empty set of ids in which every id waits on another id *of the
set*.  A literal cycle `a → b → … → a` is such a set; a set with no such subset
has an order in which every dependency comes first. -/
def Deadlocked (p : PlanCore) (c : List Id) : Prop :=
  c ≠ [] ∧ ∀ i ∈ c, ∃ j ∈ c, j ∈ depsOf p i

/-! #### §4.2's section discipline, and §4.3's per-file-kind shapes -/

/-- §4.2's three meaningful names, each only where it means something:
`# Demoted` is a month-file section (§6.3) and `# Pinned` is a day-file section
(§6.2).  Anywhere else the same words would be an organisational heading that
reads like a rule. -/
def headingsWf (kind : DocKind) (d : Doc) : Bool :=
  d.prose.all (fun q =>
    if isHeading q.2 then
      match secKind q.2 with
      | .demoted => kind == DocKind.month
      | .pinned  => kind == DocKind.day
      | _        => true
    else true)

/-- §4.3's day file: its item lines are the `# Pinned` ones.  Everything else in
a day file — the generated plan block, `## Log`, `## Notes` — is prose, which is
why `# Pinned` is the one section a day file can put an item in. -/
def placementSectionWf (p : PlanCore) (s : Site) : Bool :=
  match docKindAt p s.doc with
  | .day => (match sectionKindAt p s with
             | some .pinned => true
             | _            => false)
  | _    => true

def sectionsWf (p : PlanCore) : Bool :=
  p.docs.all (fun d => headingsWf (docKind d) d) &&
  p.store.dom.all (fun i =>
    match p.store.get i with
    | none   => true
    | some e => placementSectionWf p e.val.live &&
        (match e.val.archiveSite with
         | none   => true
         | some r => placementSectionWf p r))

/-- **A duration the line writes is positive**, without asking what a block is.
`config.block_min` lives at the boundary (§3.1: "`b` converts via
config.block_min"), so a rule that has to hold of *every* configuration cannot
multiply — and it does not need to: `0b`, `0m`, `0h` and `0h0m` are zero at
every `block_min`, and nothing else is zero at any of them. -/
def durPositive : Dur → Bool
  | .simple n _ => decide (0 < n)
  | .hm h m     => decide (0 < h * 60 + m)

/-- How long the shape says the thing takes, where the shape says it at all.
The interval case measures the two `DT`s and says so in minutes; the window
case hands back the `dur:` **as written**, unit included, because §4.1 says a
rewrite keeps the unit. -/
def declaredDur (c : Core) : Option Dur :=
  match c.shape with
  | .window _ dv  => some dv
  | .interval a b => some (.simple (b.abs - a.abs) .minutes)
  | _             => none

/-- §4.3's four file-kind rules, as one function of the kind.

* **routines**: "every line is `open`, has a window or `after-done`".
* **optional**: `open`, and it must say how long it takes — a bare `dur:` on an
  optional line is an all-day window in this model, which is the reading that
  makes §4.3's `- Severance S3E4  dur:1h` a `Shape`.
* **calendar**: "generated intervals".
* **month**: "roots carry explicit priority … they are outcomes, not work"
  (§6.2) — an outcome carries no date, so a month item's shape is `none`.

Every other kind — backlog, week, day, and any path outside §2's layout — has
no shape rule, which is what §4.3 says about them. -/
def shapeWfFor : DocKind → Core → Bool
  | .routines, c =>
      (c.scope == Scope.openEnded) &&
      (match c.shape, c.recur with
       | .window _ _, _  => true
       | _,           .afterDone _ => true
       | _,           _  => false)
  | .optional, c =>
      (c.scope == Scope.openEnded) &&
      (match declaredDur c with
       | some dv => durPositive dv
       | none    => false)
  | .calendar, c => (match c.shape with | .interval _ _ => true | _ => false)
  | .month,    c => (c.shape == Shape.none)
  | _,         _ => true

def shapesWf (p : PlanCore) : Bool :=
  p.store.dom.all (fun i =>
    match p.store.get i with
    | none   => true
    | some e => shapeWfFor (docKindAt p e.val.live.doc) e.val)

/-- The item half of the plan-level tier, in one Bool. -/
def itemsWf (p : PlanCore) : Bool :=
  normalized p && parentsTotal p && parentsAcyclic p && afterTotal p && afterAcyclic p &&
    sectionsWf p && shapesWf p

theorem itemsWf_parts {p : PlanCore} (h : itemsWf p = true) :
    normalized p = true ∧ parentsTotal p = true ∧ parentsAcyclic p = true ∧
      afterTotal p = true ∧ afterAcyclic p = true ∧ sectionsWf p = true ∧
      shapesWf p = true := by
  simp only [itemsWf, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem itemsWf_of_parts {p : PlanCore} (h1 : normalized p = true) (h2 : parentsTotal p = true)
    (h3 : parentsAcyclic p = true) (h4 : afterTotal p = true) (h5 : afterAcyclic p = true)
    (h6 : sectionsWf p = true) (h7 : shapesWf p = true) : itemsWf p = true := by
  simp [itemsWf, h1, h2, h3, h4, h5, h6, h7]

def planWf (p : PlanCore) : Bool :=
  docsWf p && sitesInRange p && pathsDistinct p && demotionsOriented p && itemsWf p

theorem planWf_parts {p : PlanCore} (h : planWf p = true) :
    docsWf p = true ∧ sitesInRange p = true ∧ pathsDistinct p = true ∧
      demotionsOriented p = true ∧ itemsWf p = true := by
  simp only [planWf, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem planWf_of_parts {p : PlanCore} (h1 : docsWf p = true) (h2 : sitesInRange p = true)
    (h3 : pathsDistinct p = true) (h4 : demotionsOriented p = true) (h5 : itemsWf p = true) :
    planWf p = true := by
  simp [planWf, h1, h2, h3, h4, h5]

/-- Which of `itemsWf`'s seven conjuncts failed, as a name a host can print.
`tm check` is the same checker, so the diagnostic and the acceptance rule cannot
drift apart. -/
def firstItemFault (p : PlanCore) : String :=
  if !normalized p then "rankCollision"
  else if !parentsTotal p then "danglingParent"
  else if !parentsAcyclic p then "parentCycle"
  else if !afterTotal p then "danglingDep"
  else if !afterAcyclic p then "depCycle"
  else if !sectionsWf p then "sectionDiscipline"
  else "fileKindShape"

/-- The plan.  You cannot make one without discharging `planWf`. -/
def WfPlan := { p : PlanCore // planWf p = true }

/-- The path a document index names.  `none` is out of range — which
`no_line_is_lost` rules out for any site a plan actually denotes. -/
def pathAt (p : PlanCore) (k : DocIx) : Option (List Char) := (p.docs[k]?).map Doc.path

/-- **No prose line is an item line.**  So the only item lines a document emits
are the ones its entities render, and `no_two_lines_of_one_id_in_one_file`
covers all of them. -/
theorem prose_is_never_an_item (p : WfPlan) (d : Doc) (hd : d ∈ p.val.docs)
    (q : Nat × List Char) (hq : q ∈ d.prose) : isItemLine q.2 = false := by
  have h1 : docWf d = true := List.all_eq_true.1 (planWf_parts p.property).1 d hd
  have h2 := List.all_eq_true.1 h1 q hq
  simpa using h2

/-- Changing the store cannot change the *document* half of the invariant, which
reads `docs` only.  The other two halves are not free of the store — that is the
point of adding them: `sitesInRange` is precisely the obligation a command that
relocates a line must re-discharge. -/
theorem docsWf_store (p : PlanCore) (s : Store) : docsWf { p with store := s } = docsWf p := rfl

theorem pathsDistinct_store (p : PlanCore) (s : Store) :
    pathsDistinct { p with store := s } = pathsDistinct p := rfl

/-! ## Nothing a plan denotes can fall off the end of `docs` -/

/-- A rendered line sits at one of the entity's own two placements. -/
theorem render_site (i : Id) (e : Entity) (l : Line) (h : l ∈ render i e) :
    l.site = e.val.live ∨ e.val.archiveSite = some l.site := by
  unfold render renderCore at h
  cases ha : e.val.archive with
  | none =>
      rw [ha] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst h; left; rfl
  | some t =>
      rw [ha] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · left; rfl
      · right; exact Core.archiveSite_some ha

theorem lines_mem (p : PlanCore) (l : Line) (h : l ∈ p.lines) :
    ∃ i e, p.store.get i = some e ∧ i ∈ p.store.dom ∧ l ∈ render i e := by
  unfold PlanCore.lines at h
  simp only [List.mem_flatMap] at h
  obtain ⟨i, hi, hl⟩ := h
  cases g : p.store.get i with
  | none => rw [g] at hl; simp at hl
  | some e => rw [g] at hl; exact ⟨i, e, g, hi, hl⟩

/-- **Nothing the kernel holds can silently disappear from the output.**  Every
line of every plan lands in a document that exists, so rendering document by
document over `docs` emits all of them.  Before `sitesInRange` joined `planWf`,
`move` to a document index past the end of `docs` deleted the item and returned
`ok`. -/
theorem no_line_is_lost (p : WfPlan) (l : Line) (h : l ∈ p.val.lines) :
    l.site.doc < p.val.docs.length := by
  obtain ⟨i, e, hget, hdom, hl⟩ := lines_mem p.val l h
  have hall := List.all_eq_true.1 (planWf_parts p.property).2.1 i hdom
  rw [hget] at hall
  simp only [entityInRange, Bool.and_eq_true, siteInRange, decide_eq_true_eq] at hall
  rcases render_site i e l hl with hs | hs
  · rw [hs]; exact hall.1
  · have := hall.2
    rw [hs] at this
    simpa [siteInRange] using this

/-- **The theorem the name always promised.**  Two lines carrying one id that
land in one *file* — the same path on disk, not merely the same list index —
are the same line.  The index-level version below is what this is proved from;
on its own it left two documents free to share a path, and then a demotion put
two `^m1` lines into one file with every stated theorem still true. -/
theorem no_two_lines_of_one_id_in_one_path (p : WfPlan) (l₁ l₂ : Line)
    (h₁ : l₁ ∈ p.val.lines) (h₂ : l₂ ∈ p.val.lines) (hid : l₁.id = l₂.id)
    (hpath : pathAt p.val l₁.site.doc = pathAt p.val l₂.site.doc) : l₁.site = l₂.site := by
  have k₁ : l₁.site.doc < p.val.docs.length := no_line_is_lost p l₁ h₁
  have k₂ : l₂.site.doc < p.val.docs.length := no_line_is_lost p l₂ h₂
  have hnd : (p.val.docs.map Doc.path).Nodup := by
    have := (planWf_parts p.property).2.2.1
    simpa [pathsDistinct] using this
  have hm₁ : l₁.site.doc < (p.val.docs.map Doc.path).length := by simpa using k₁
  have hm₂ : l₂.site.doc < (p.val.docs.map Doc.path).length := by simpa using k₂
  have heq : (p.val.docs.map Doc.path)[l₁.site.doc] = (p.val.docs.map Doc.path)[l₂.site.doc] := by
    simp only [List.getElem_map]
    have e₁ : pathAt p.val l₁.site.doc = some (p.val.docs[l₁.site.doc]).path := by
      simp [pathAt, List.getElem?_eq_getElem k₁]
    have e₂ : pathAt p.val l₂.site.doc = some (p.val.docs[l₂.site.doc]).path := by
      simp [pathAt, List.getElem?_eq_getElem k₂]
    rw [e₁, e₂] at hpath
    exact Option.some.inj hpath
  have hk : l₁.site.doc = l₂.site.doc := (List.getElem_inj hnd).mp heq
  exact no_two_lines_of_one_id_in_one_file p.val l₁ l₂ h₁ h₂ hid hk

/-- **Which of a demotion's two lines is the tombstone is a fact about the
plan, not a guess** — and where the boxes do not say, the files do.  In every
accepted plan, an entity whose record *also* reads `[-]` has its archive
placement in a horizon strictly before the record's, so the two are never
interchangeable.  This is what the loader inverts when the glyphs tie, and
`horizonPrecedes_asymm` is why the inversion has one answer.

`hglyph` is the hypothesis this theorem gained and it is load-bearing: drop it
and the statement is false of §4.3's own fixture, where the record is a `[ ]`
in `week/2026-W37.md` and the archive a `[-]` in `month/2026-09.md`.  There the
conclusion fails and nothing is wrong — the boxes settle that pair without
consulting a file. -/
theorem the_tombstone_is_behind_the_live_line (p : WfPlan) (i : Id) (e : Entity) (r : Site)
    (hget : p.val.store.get i = some e) (harch : e.val.archiveSite = some r)
    (hglyph : glyphOfStatus e.val.status = Glyph.demoted) :
    horizonPrecedes (docRegion p.val r.doc) (docRegion p.val e.val.live.doc) = true := by
  have hdom : i ∈ p.val.store.dom := (p.val.store.domSpec i).mpr (by rw [hget]; rfl)
  have hall := List.all_eq_true.1 (planWf_parts p.property).2.2.2.1 i hdom
  rw [hget] at hall
  cases ha : e.val.archive with
  | none => rw [Core.archiveSite_none ha] at harch; simp at harch
  | some t =>
      rw [Core.archiveSite_some ha] at harch
      simp only [Option.some.injEq] at harch
      subst harch
      simpa [demotionOriented, ha, hglyph] using hall

/-! ## Documents: splitting text into prose and items, and putting it back -/

structure DocSplit where
  prose : List (Nat × List Char)
  items : List (Nat × (Id × Glyph × RawItem))
deriving Repr, Inhabited

/-- Read a file.  Rank = line index, so ranks are distinct by construction and
`Normalized` is not a predicate anyone has to maintain. -/
def splitDoc (k : Nat) (ls : List (List Char)) : DocSplit :=
  match ls with
  | []      => ⟨[], []⟩
  | l :: rest =>
    let d := splitDoc (k + 1) rest
    match parseItem l with
    | .ok (i, g, r) => ⟨d.prose, (k, i, g, r) :: d.items⟩
    | .error _      => ⟨(k, l) :: d.prose, d.items⟩

/-- Merge two rank-ordered lists of lines. -/
def weave (ps is : List (Nat × List Char)) : List (List Char) :=
  match ps, is with
  | [], js => js.map Prod.snd
  | qs, [] => qs.map Prod.snd
  | (a, x) :: ps', (b, y) :: is' =>
      if a ≤ b then x :: weave ps' ((b, y) :: is') else y :: weave ((a, x) :: ps') is'
termination_by ps.length + is.length

def renderSplit (d : DocSplit) : List (List Char) :=
  weave d.prose (d.items.map (fun p => (p.1, serializeItem p.2.1 p.2.2.1 p.2.2.2)))

theorem weave_nil_right (ps : List (Nat × List Char)) : weave ps [] = ps.map Prod.snd := by
  cases ps with
  | nil => rw [weave]
  | cons q qs => rw [weave]; simp

theorem weave_item_first (ps : List (Nat × List Char)) (b : Nat) (y : List Char)
    (is : List (Nat × List Char)) (h : ∀ p ∈ ps, b < p.1) :
    weave ps ((b, y) :: is) = y :: weave ps is := by
  cases ps with
  | nil =>
      cases is with
      | nil => simp [weave]
      | cons q qs => simp [weave]
  | cons p ps' =>
      obtain ⟨a, x⟩ := p
      have hba : b < a := h (a, x) (by simp)
      have : ¬ (a ≤ b) := by omega
      rw [weave]
      simp only [this, if_false]

theorem weave_prose_first (b : Nat) (x : List Char) (ps is : List (Nat × List Char))
    (h : ∀ p ∈ is, b ≤ p.1) : weave ((b, x) :: ps) is = x :: weave ps is := by
  cases is with
  | nil => rw [weave_nil_right, weave_nil_right]; simp
  | cons q qs =>
      obtain ⟨c, y⟩ := q
      have hbc : b ≤ c := h (c, y) (by simp)
      rw [weave]
      simp only [hbc, if_true]

theorem splitDoc_prose_ge (k : Nat) (ls : List (List Char)) :
    ∀ p ∈ (splitDoc k ls).prose, k ≤ p.1 := by
  induction ls generalizing k with
  | nil => intro p hp; simp [splitDoc] at hp
  | cons l rest ih =>
      intro p hp
      unfold splitDoc at hp
      simp only at hp
      split at hp
      · have := ih (k + 1) p hp; omega
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp
        · have := ih (k + 1) p hp; omega

theorem splitDoc_items_ge (k : Nat) (ls : List (List Char)) :
    ∀ p ∈ (splitDoc k ls).items, k ≤ p.1 := by
  induction ls generalizing k with
  | nil => intro p hp; simp [splitDoc] at hp
  | cons l rest ih =>
      intro p hp
      unfold splitDoc at hp
      simp only at hp
      split at hp
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp
        · have := ih (k + 1) p hp; omega
      · have := ih (k + 1) p hp; omega

/-- Prose is what did **not** parse as an item, so a loaded document satisfies
`docWf` by construction — `parse`'s success value is a `WfPlan`, not a value
that a separate validator later blesses. -/
theorem splitDoc_prose_not_item (k : Nat) (ls : List (List Char)) :
    ∀ q ∈ (splitDoc k ls).prose, isItemLine q.2 = false := by
  induction ls generalizing k with
  | nil => intro q hq; simp [splitDoc] at hq
  | cons l rest ih =>
      intro q hq
      unfold splitDoc at hq
      simp only at hq
      split at hq
      · exact ih (k + 1) q hq
      · rename_i e he
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · simp [isItemLine, he]
        · exact ih (k + 1) q hq

/-- **Round trip over a whole file.**  Splitting a document into prose and
items and putting it back reproduces the file byte for byte — including every
item line, whose state box and `^id` were *regenerated* rather than copied. -/
theorem renderSplit_splitDoc (k : Nat) (ls : List (List Char)) :
    renderSplit (splitDoc k ls) = ls := by
  induction ls generalizing k with
  | nil => simp [renderSplit, splitDoc, weave]
  | cons l rest ih =>
      unfold splitDoc
      simp only
      cases hp : parseItem l with
      | ok trip =>
          obtain ⟨i, g, r⟩ := trip
          simp only [renderSplit, List.map_cons]
          rw [weave_item_first _ k _ _ ?_]
          · rw [serialize_parse l i g r hp]
            have := ih (k + 1)
            unfold renderSplit at this
            rw [this]
          · intro q hq
            have := splitDoc_prose_ge (k + 1) rest q hq
            omega
      | error e =>
          simp only [renderSplit]
          rw [weave_prose_first _ _ _ _ ?_]
          · have := ih (k + 1)
            unfold renderSplit at this
            rw [this]
          · intro q hq
            simp only [List.mem_map] at hq
            obtain ⟨w, hw, rfl⟩ := hq
            have := splitDoc_items_ge (k + 1) rest w hw
            simp only
            omega


/-! ## Rank order: the three lemmas the *plan-level* round trip needs

`renderSplit_splitDoc` is the round trip for one file's text.  The plan-level
round trip has to survive a detour the file never takes: the item lines are
taken apart, stored under their ids, and read back out **in the order the store
enumerates its domain**, which is not rank order.  Something has to put them
back in order, and that something must be a *reconstruction* and not a choice —
otherwise the bytes a host receives depend on the order it happened to list its
documents in, which is the same defect `orientPair_comm` removes for the
demotion pair.

Three facts do it, and none of them needs Mathlib:

* a list ordered strictly by rank is **determined by its members**
  (`sorted_ext_by_key`) — so any correct sort of the store's lines is *the*
  file's line list, whatever order the store was in;
* `splitDoc` produces prose in non-decreasing and items in **strictly
  increasing** rank order (`splitDoc_prose_sorted`, `splitDoc_items_sorted`),
  because a rank is a line index;
* rank distinctness — `Normalized`, which joined `planWf` — is what makes
  "strictly" available on the store's side.
-/

/-- `splitDoc` in three rewriting steps, so every later proof about it is a
`rw` and not a `split`. -/
theorem splitDoc_nil (k : Nat) : splitDoc k [] = ⟨[], []⟩ := rfl

theorem splitDoc_cons_ok (k : Nat) (l : List Char) (rest : List (List Char))
    (i : Id) (g : Glyph) (r : RawItem) (h : parseItem l = .ok (i, g, r)) :
    splitDoc k (l :: rest) =
      ⟨(splitDoc (k + 1) rest).prose, (k, i, g, r) :: (splitDoc (k + 1) rest).items⟩ := by
  simp only [splitDoc, h]

theorem splitDoc_cons_error (k : Nat) (l : List Char) (rest : List (List Char))
    (e : PErr) (h : parseItem l = .error e) :
    splitDoc k (l :: rest) =
      ⟨(k, l) :: (splitDoc (k + 1) rest).prose, (splitDoc (k + 1) rest).items⟩ := by
  simp only [splitDoc, h]

/-- **A list ordered strictly by a key is determined by its members.**  Two
strictly ordered lists with the same elements are the same list — so "sort the
store's lines by rank" has one answer and it does not depend on the order the
store handed them over. -/
theorem sorted_ext_by_key {α : Type} (key : α → Nat) : ∀ (l₁ l₂ : List α),
    l₁.Pairwise (fun a b => key a < key b) → l₂.Pairwise (fun a b => key a < key b) →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ _ _ h
      cases l₂ with
      | nil => rfl
      | cons b t => exact absurd ((h b).2 (by simp)) (by simp)
  | cons a t ih =>
      intro l₂ h₁ h₂ h
      cases l₂ with
      | nil => exact absurd ((h a).1 (by simp)) (by simp)
      | cons b s =>
          rw [List.pairwise_cons] at h₁ h₂
          have hab : a = b := by
            rcases List.mem_cons.1 ((h a).1 (by simp)) with hx | hx
            · exact hx
            · rcases List.mem_cons.1 ((h b).2 (by simp)) with hy | hy
              · exact hy.symm
              · exact absurd (Nat.lt_trans (h₁.1 b hy) (h₂.1 a hx)) (Nat.lt_irrefl _)
          subst hab
          have hmem : ∀ x, x ∈ t ↔ x ∈ s := by
            intro x
            constructor
            · intro hx
              rcases List.mem_cons.1 ((h x).1 (by simp [hx])) with he | hs
              · exact absurd (he ▸ h₁.1 x hx) (Nat.lt_irrefl _)
              · exact hs
            · intro hx
              rcases List.mem_cons.1 ((h x).2 (by simp [hx])) with he | hs
              · exact absurd (he ▸ h₂.1 x hx) (Nat.lt_irrefl _)
              · exact hs
          rw [ih s h₁.2 h₂.2 hmem]

/-- Prose comes out of a file in rank order, because a rank **is** a line
index. -/
theorem splitDoc_prose_sorted : ∀ (k : Nat) (ls : List (List Char)),
    (splitDoc k ls).prose.Pairwise (fun a b => a.1 ≤ b.1) := by
  intro k ls
  induction ls generalizing k with
  | nil => simp [splitDoc_nil]
  | cons l rest ih =>
      cases hp : parseItem l with
      | ok trip =>
          obtain ⟨i, g, r⟩ := trip
          rw [splitDoc_cons_ok k l rest i g r hp]
          exact ih (k + 1)
      | error e =>
          rw [splitDoc_cons_error k l rest e hp]
          refine List.pairwise_cons.2 ⟨?_, ih (k + 1)⟩
          intro q hq
          have := splitDoc_prose_ge (k + 1) rest q hq
          omega

/-- And the item lines come out **strictly** ordered, which is what
`sorted_ext_by_key` needs on the file's side of the round trip. -/
theorem splitDoc_items_sorted : ∀ (k : Nat) (ls : List (List Char)),
    (splitDoc k ls).items.Pairwise (fun a b => a.1 < b.1) := by
  intro k ls
  induction ls generalizing k with
  | nil => simp [splitDoc_nil]
  | cons l rest ih =>
      cases hp : parseItem l with
      | ok trip =>
          obtain ⟨i, g, r⟩ := trip
          rw [splitDoc_cons_ok k l rest i g r hp]
          refine List.pairwise_cons.2 ⟨?_, ih (k + 1)⟩
          intro q hq
          have := splitDoc_items_ge (k + 1) rest q hq
          omega
      | error e =>
          rw [splitDoc_cons_error k l rest e hp]
          exact ih (k + 1)

/-- Strict order out of a weak one and distinct keys.  The weak order is what
insertion sort gives; the distinctness is `Normalized`. -/
theorem pairwise_lt_of_le_ne {α : Type} (key : α → Nat) : ∀ {l : List α},
    l.Pairwise (fun a b => key a ≤ key b) → l.Pairwise (fun a b => key a ≠ key b) →
    l.Pairwise (fun a b => key a < key b) := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons x xs ih =>
      intro h1 h2
      rw [List.pairwise_cons] at h1 h2 ⊢
      exact ⟨fun b hb => Nat.lt_of_le_of_ne (h1.1 b hb) (h2.1 b hb), ih h1.2 h2.2⟩

/-- `Nodup` of the keys is `Pairwise` of key-distinctness on the list. -/
theorem pairwise_ne_of_nodup_keys {α : Type} (key : α → Nat) {l : List α}
    (h : (l.map key).Nodup) : l.Pairwise (fun a b => key a ≠ key b) := by
  rw [show ((l.map key).Nodup) = ((l.map key).Pairwise (· ≠ ·)) from rfl,
    List.pairwise_map] at h
  exact h


/-! ## Acyclicity, twice, over a finite domain and without Mathlib

The parent relation is a partial **function**, so its cycles are found by
walking; the `after:` relation is a **relation**, so its cycles are found by
peeling.  Each check is proved in both directions, because a checker joined
into `planWf` that is merely *sound* would refuse plans that are fine, and one
that is merely *complete* would accept plans that are not.
-/

theorem anc_zero (p : PlanCore) (i : Id) : anc p 0 i = some i := rfl

theorem anc_succ_none (p : PlanCore) (n : Nat) (i : Id) (h : parentStep p i = none) :
    anc p (n + 1) i = none := by simp [anc, h]

theorem anc_succ_some (p : PlanCore) (n : Nat) (i j : Id) (h : parentStep p i = some j) :
    anc p (n + 1) i = anc p n j := by simp [anc, h]

/-- The chain only gets shorter: once it has run out it stays out. -/
theorem anc_none_mono (p : PlanCore) : ∀ n i, anc p n i = none → anc p (n + 1) i = none := by
  intro n
  induction n with
  | zero => intro i h; simp [anc] at h
  | succ m ih =>
      intro i h
      cases hs : parentStep p i with
      | none   => exact anc_succ_none p _ i hs
      | some j =>
          rw [anc_succ_some p _ i j hs]
          rw [anc_succ_some p _ i j hs] at h
          exact ih j h

theorem anc_none_add (p : PlanCore) (a : Nat) (i : Id) (h : anc p a i = none) :
    ∀ b, anc p (a + b) i = none := by
  intro b
  induction b with
  | zero => exact h
  | succ c ih => exact anc_none_mono p _ i ih

/-- Walking `a` links and then `b` more is walking `a + b`. -/
theorem anc_add (p : PlanCore) : ∀ a b i,
    anc p (a + b) i = (match anc p a i with | none => none | some x => anc p b x) := by
  intro a
  induction a with
  | zero => intro b i; simp [anc]
  | succ m ih =>
      intro b i
      cases hs : parentStep p i with
      | none =>
          rw [show m + 1 + b = (m + b) + 1 from by omega, anc_succ_none p _ i hs,
            anc_succ_none p _ i hs]
      | some j =>
          rw [show m + 1 + b = (m + b) + 1 from by omega, anc_succ_some p _ i j hs,
            anc_succ_some p _ i j hs]
          exact ih b j

/-- The chain of `i`, `n` links long or as far as it goes. -/
def chainOf (p : PlanCore) : Nat → Id → List Id
  | 0,     _ => []
  | n + 1, i => i :: (match parentStep p i with
                      | none   => []
                      | some j => chainOf p n j)

theorem chainOf_succ_none (p : PlanCore) (n : Nat) (i : Id) (h : parentStep p i = none) :
    chainOf p (n + 1) i = [i] := by simp [chainOf, h]

theorem chainOf_succ_some (p : PlanCore) (n : Nat) (i j : Id) (h : parentStep p i = some j) :
    chainOf p (n + 1) i = i :: chainOf p n j := by simp [chainOf, h]

/-- If the chain survives `n` links it has visited `n + 1` ids. -/
theorem chainOf_length (p : PlanCore) : ∀ n i, anc p n i ≠ none →
    (chainOf p (n + 1) i).length = n + 1 := by
  intro n
  induction n with
  | zero =>
      intro i _
      cases hs : parentStep p i <;> simp [chainOf, hs]
  | succ m ih =>
      intro i h
      cases hs : parentStep p i with
      | none   => rw [anc_succ_none p m i hs] at h; exact absurd rfl h
      | some j =>
          rw [anc_succ_some p m i j hs] at h
          rw [chainOf_succ_some p (m + 1) i j hs, List.length_cons, ih j h]

/-- Every id on the chain is an id of the plan — which is what `parentsTotal`
buys, and it is the hypothesis the pigeonhole needs. -/
theorem chainOf_mem_dom (p : PlanCore) (htot : parentsTotal p = true) :
    ∀ n i, i ∈ p.store.dom → ∀ x ∈ chainOf p n i, x ∈ p.store.dom := by
  intro n
  induction n with
  | zero => intro i _ x hx; simp [chainOf] at hx
  | succ m ih =>
      intro i hi x hx
      cases hs : parentStep p i with
      | none =>
          rw [chainOf_succ_none p m i hs] at hx
          simp only [List.mem_singleton] at hx
          exact hx ▸ hi
      | some j =>
          have hj : j ∈ p.store.dom := by
            have := List.all_eq_true.1 htot i hi
            rw [hs] at this
            exact (p.store.domSpec j).mpr this
          rw [chainOf_succ_some p m i j hs] at hx
          rcases List.mem_cons.1 hx with rfl | hx'
          · exact hi
          · exact ih j hj x hx'

/-- Every id on the chain is an ancestor of its head. -/
theorem chainOf_mem_anc (p : PlanCore) : ∀ n i x, x ∈ chainOf p n i → ∃ k, anc p k i = some x := by
  intro n
  induction n with
  | zero => intro i x hx; simp [chainOf] at hx
  | succ m ih =>
      intro i x hx
      cases hs : parentStep p i with
      | none =>
          rw [chainOf_succ_none p m i hs] at hx
          simp only [List.mem_singleton] at hx
          exact ⟨0, by rw [hx]; exact anc_zero p i⟩
      | some j =>
          rw [chainOf_succ_some p m i j hs] at hx
          rcases List.mem_cons.1 hx with rfl | hx'
          · exact ⟨0, rfl⟩
          · obtain ⟨k, hk⟩ := ih j x hx'
            exact ⟨k + 1, by rw [anc_succ_some p k i j hs]; exact hk⟩

/-- **A repeat on the chain is a cycle.**  This is the half of the pigeonhole
argument that does the work; the counting half is
`List.Nodup.length_le_of_subset` from core. -/
theorem chain_dup_gives_cycle (p : PlanCore) :
    ∀ n i, ¬ (chainOf p n i).Nodup → ∃ j, OnACycle p j := by
  intro n
  induction n with
  | zero => intro i h; exact absurd (by simp [chainOf]) h
  | succ m ih =>
      intro i h
      cases hs : parentStep p i with
      | none => rw [chainOf_succ_none p m i hs] at h; exact absurd (by simp) h
      | some j =>
          rw [chainOf_succ_some p m i j hs, List.nodup_cons] at h
          by_cases hmem : i ∈ chainOf p m j
          · obtain ⟨k, hk⟩ := chainOf_mem_anc p m j i hmem
            exact ⟨i, k + 1, Nat.succ_pos k, by rw [anc_succ_some p k i j hs]; exact hk⟩
          · exact ih j (fun hc => h ⟨hmem, hc⟩)

/-- **Soundness: the check means what its name says.**  In a plan the checker
accepts, no stored id is its own proper ancestor — so `@parent` is a forest and
§3.2's `root(item)` is a walk that ends. -/
theorem parentsAcyclic_sound (p : PlanCore) (h : parentsAcyclic p = true)
    (i : Id) (hi : i ∈ p.store.dom) : ¬ OnACycle p i := by
  rintro ⟨n, hn, hc⟩
  have key : ∀ m, anc p (m * n) i = some i := by
    intro m
    induction m with
    | zero => rw [Nat.zero_mul]; exact anc_zero p i
    | succ k ih =>
        rw [Nat.succ_mul, anc_add, ih]
        exact hc
  have hall := List.all_eq_true.1 h i hi
  have hnone : anc p (fuel p) i = none := by
    simpa [Option.isNone_iff_eq_none] using hall
  have hbig : anc p (fuel p * n) i = none := by
    rw [show fuel p * n = fuel p + (fuel p * n - fuel p) from by
      have : fuel p ≤ fuel p * n := Nat.le_mul_of_pos_right _ hn
      omega]
    exact anc_none_add p _ i hnone _
  rw [key (fuel p)] at hbig
  exact absurd hbig (by simp)

/-- **The bound is enough.**  `|dom| + 1` links is not a guess: a chain that
long has visited `|dom| + 1` ids of a `Nodup` domain of size `|dom|`, so two of
them are the same id and that is a cycle.  So the checker never rejects a plan
whose parents really are acyclic, and "decidable by bounded iteration" costs no
generality. -/
theorem parentsAcyclic_complete (p : PlanCore) (htot : parentsTotal p = true)
    (hno : ∀ j, ¬ OnACycle p j) : parentsAcyclic p = true := by
  simp only [parentsAcyclic, List.all_eq_true]
  intro i hi
  simp only [Option.isNone_iff_eq_none]
  cases hne0 : anc p (fuel p) i with
  | none => rfl
  | some z =>
  exfalso
  have hne : anc p (fuel p) i ≠ none := by rw [hne0]; simp
  have hN : anc p p.store.dom.length i ≠ none := by
    intro hc
    exact hne (anc_none_add p _ i hc 1)
  have hlen : (chainOf p (p.store.dom.length + 1) i).length = p.store.dom.length + 1 :=
    chainOf_length p _ i hN
  have hsub : chainOf p (p.store.dom.length + 1) i ⊆ p.store.dom :=
    fun {x} hx => chainOf_mem_dom p htot _ i hi x hx
  have hnd : (chainOf p (p.store.dom.length + 1) i).Nodup := by
    match hdec : decide ((chainOf p (p.store.dom.length + 1) i).Nodup) with
    | true  => exact of_decide_eq_true hdec
    | false =>
        obtain ⟨j, hj⟩ := chain_dup_gives_cycle p _ i (of_decide_eq_false hdec)
        exact absurd hj (hno j)
  have := List.Nodup.length_le_of_subset hnd hsub
  omega

/-- **And the check bites**: an item that is its own parent is not a plan. -/
theorem self_parent_is_rejected (p : PlanCore) (i : Id) (hi : i ∈ p.store.dom)
    (h : parentStep p i = some i) : parentsAcyclic p = false := by
  have key : ∀ n, anc p n i = some i := by
    intro n
    induction n with
    | zero => exact anc_zero p i
    | succ m ih => rw [anc_succ_some p m i i h]; exact ih
  cases hb : parentsAcyclic p with
  | false => rfl
  | true =>
      have hall := List.all_eq_true.1 hb i hi
      rw [key (fuel p)] at hall
      simp at hall

/-! ### `after:`: the peel, and the deadlocked set -/

theorem peelN_nil (p : PlanCore) : ∀ n, peelN p n [] = [] := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih => show peelN p m (peel p []) = []; simpa [peel] using ih

theorem peel_eq_or_lt (p : PlanCore) (r : List Id) :
    peel p r = r ∨ (peel p r).length < r.length := by
  rcases Nat.lt_or_ge (peel p r).length r.length with h | h
  · exact Or.inr h
  · exact Or.inl (List.Sublist.eq_of_length_le List.filter_sublist h)

/-- Peeling `|r|` times either clears the set or reaches a **fixed point that
is not empty** — and there is no third outcome, because a peel that changes
anything strictly shortens the list.  This is where the bound `|dom|` comes
from, and it is arithmetic rather than pigeonhole. -/
theorem peelN_empty_or_fixed (p : PlanCore) : ∀ n r, r.length ≤ n →
    peelN p n r = [] ∨ ∃ s, s ≠ [] ∧ peel p s = s := by
  intro n
  induction n with
  | zero =>
      intro r hr
      left
      have : r = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hr)
      simpa [peelN] using this
  | succ m ih =>
      intro r hr
      rcases peel_eq_or_lt p r with heq | hlt
      · by_cases hnil : r = []
        · left
          subst hnil
          show peelN p m (peel p []) = []
          simpa [peel] using peelN_nil p m
        · exact Or.inr ⟨r, hnil, heq⟩
      · have hle : (peel p r).length ≤ m := by omega
        exact ih (peel p r) hle

/-- A non-empty fixed point of the peel is exactly a deadlocked set. -/
theorem fixed_is_deadlocked (p : PlanCore) (s : List Id) (hs : s ≠ []) (hfix : peel p s = s) :
    Deadlocked p s := by
  refine ⟨hs, ?_⟩
  intro i hi
  have hmem : i ∈ peel p s := by rw [hfix]; exact hi
  have hq := (List.mem_filter.1 hmem).2
  simp only [List.any_eq_true, decide_eq_true_eq] at hq
  obtain ⟨j, hj1, hj2⟩ := hq
  exact ⟨j, hj2, hj1⟩

/-- A deadlocked set is never struck out: every one of its ids still waits on
one of its ids, whatever else has gone. -/
theorem deadlocked_survives_peel (p : PlanCore) (c r : List Id) (hd : Deadlocked p c)
    (hsub : ∀ x ∈ c, x ∈ r) : ∀ x ∈ c, x ∈ peel p r := by
  intro i hi
  refine List.mem_filter.2 ⟨hsub i hi, ?_⟩
  obtain ⟨j, hj, hjd⟩ := hd.2 i hi
  simp only [List.any_eq_true, decide_eq_true_eq]
  exact ⟨j, hjd, hsub j hj⟩

theorem deadlocked_survives_peelN (p : PlanCore) (c : List Id) (hd : Deadlocked p c) :
    ∀ n r, (∀ x ∈ c, x ∈ r) → ∀ x ∈ c, x ∈ peelN p n r := by
  intro n
  induction n with
  | zero => intro r h; exact h
  | succ m ih => intro r h; exact ih (peel p r) (deadlocked_survives_peel p c r hd h)

/-- **Soundness.**  In a plan the checker accepts there is no deadlocked set of
stored ids — §5.5's "cycles are a `tm check` error", except that here the cyclic
plan is not a value. -/
theorem afterAcyclic_sound (p : PlanCore) (h : afterAcyclic p = true) (c : List Id)
    (hc : ∀ x ∈ c, x ∈ p.store.dom) : ¬ Deadlocked p c := by
  intro hd
  cases hcs : c with
  | nil => exact hd.1 hcs
  | cons a t =>
      have hmem : a ∈ c := by rw [hcs]; simp
      have := deadlocked_survives_peelN p c hd p.store.dom.length p.store.dom hc a hmem
      simp only [afterAcyclic, List.isEmpty_iff] at h
      rw [h] at this
      simp at this

/-- **The bound is enough here too**, and by counting rather than pigeonhole:
`|dom|` peels either clear the domain or reach a non-empty fixed point, and a
non-empty fixed point *is* a deadlocked set. -/
theorem afterAcyclic_complete (p : PlanCore) (hno : ∀ c, ¬ Deadlocked p c) :
    afterAcyclic p = true := by
  rcases peelN_empty_or_fixed p p.store.dom.length p.store.dom (Nat.le_refl _) with
    h | ⟨s, hs, hfix⟩
  · simp [afterAcyclic, h]
  · exact absurd (fixed_is_deadlocked p s hs hfix) (hno s)

/-- **And it bites**: `after:^self` is not a plan. -/
theorem self_dep_is_rejected (p : PlanCore) (i : Id) (hi : i ∈ p.store.dom)
    (h : i ∈ depsOf p i) : afterAcyclic p = false := by
  have hd : Deadlocked p [i] := by
    refine ⟨by simp, ?_⟩
    intro x hx
    simp only [List.mem_singleton] at hx
    exact ⟨x, by simp [hx], by rw [hx]; exact h⟩
  have hsub : ∀ x ∈ [i], x ∈ p.store.dom := by
    intro x hx
    simp only [List.mem_singleton] at hx
    exact hx ▸ hi
  cases hb : afterAcyclic p with
  | false => rfl
  | true  => exact absurd hd (afterAcyclic_sound p hb [i] hsub)


/-! ## `Normalized`: a `(document, rank)` names one line

`no_two_lines_of_one_id_in_one_path` says an id names at most one line per file.
This is the other direction — a *position* names at most one line — and together
they make the correspondence between the store and the bytes on disk a
bijection.  It is also what makes `weave` (the document round trip) an order and
not a choice: with two lines at one rank, which came first would depend on the
fold order rather than on the file. -/

theorem nodup_map_inj {α β} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x t ih =>
      intro h a ha b hb hfab
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
      rcases List.mem_cons.1 ha with rfl | ha'
      · rcases List.mem_cons.1 hb with rfl | hb'
        · rfl
        · exact absurd ⟨b, hb', hfab.symm⟩ h.1
      · rcases List.mem_cons.1 hb with rfl | hb'
        · exact absurd ⟨a, ha', hfab⟩ h.1
        · exact ih h.2 a ha' b hb' hfab

/-- Shorthand: every accepted plan passes the item half of the checker. -/
theorem WfPlan.items (p : WfPlan) : itemsWf p.val = true := (planWf_parts p.property).2.2.2.2

/-- **A site names one line.**  Two lines of an accepted plan that sit in the
same document at the same rank are the same line — same id, same bytes. -/
theorem site_names_one_line (p : WfPlan) (l₁ l₂ : Line)
    (h₁ : l₁ ∈ p.val.lines) (h₂ : l₂ ∈ p.val.lines) (hs : l₁.site = l₂.site) : l₁ = l₂ := by
  have hk : l₁.site.doc < p.val.docs.length := no_line_is_lost p l₁ h₁
  have hnorm := (itemsWf_parts p.items).1
  simp only [normalized, List.all_eq_true] at hnorm
  have hnd : (docRanks p.val l₁.site.doc).Nodup := by
    have := hnorm l₁.site.doc (List.mem_range.2 hk)
    simpa using this
  have hnd2 : ((p.val.lines.filter (fun l => l.site.doc == l₁.site.doc)).map
      (fun l => l.site.rank)).Nodup := by
    refine List.Nodup.sublist ?_ hnd
    unfold docRanks
    exact List.sublist_append_right _ _
  have m₁ : l₁ ∈ p.val.lines.filter (fun l => l.site.doc == l₁.site.doc) := by
    simp [List.mem_filter, h₁]
  have m₂ : l₂ ∈ p.val.lines.filter (fun l => l.site.doc == l₁.site.doc) := by
    simp [List.mem_filter, h₂, hs]
  exact nodup_map_inj hnd2 l₁ m₁ l₂ m₂ (by rw [hs])

/-! ### Replacing one entity: what the plan's line list does

`mapAt` re-establishes `planWf` by *computation* on every post-state, and that
is the discipline.  But a decidable re-check that no command can be shown to
pass is a trapdoor, and for `Normalized` the passing argument was missing: the
boundary always moves a line to `freshRank`, `freshRank_gt` proves that rank is
above every rank already in the destination, and the step from there to "and so
the post-state is still `Normalized`" was not written (README gap 11).

The step needs one lemma, and this is it.  A single-entity update leaves the
store's domain alone, so the plan's line list is the old one with **exactly this
entity's lines swapped out in place** — same prefix, same suffix.  Everything
that has to be said about a command's effect on *positions* is said here, once,
and `normalized_set` below turns it into the preservation proof. -/

theorem flatMap_congr {α β : Type} (l : List α) (f g : α → List β)
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.flatMap_cons, List.flatMap_cons, h a (by simp),
        ih (fun x hx => h x (by simp [hx]))]

theorem site_eq (s t : Site) (hd : s.doc = t.doc) (hr : s.rank = t.rank) : s = t := by
  cases s; cases t; simp_all

/-- **The replacement lemma for `PlanCore.lines` under a single-entity
update.**  The domain does not move, so neither does anything else: the two
line lists differ in one contiguous block, and every line outside that block
carries a different id. -/
theorem lines_set (p : PlanCore) (i : Id) (e e' : Entity)
    (hs : (p.store.get i).isSome = true) (hget : p.store.get i = some e) :
    ∃ A C : List Line,
      p.lines = A ++ (render i e ++ C) ∧
      PlanCore.lines { p with store := p.store.set i e' hs } = A ++ (render i e' ++ C) ∧
      (∀ l ∈ A, l.id ≠ i) ∧ (∀ l ∈ C, l.id ≠ i) := by
  have hdom : i ∈ p.store.dom := (p.store.domSpec i).mpr hs
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hdom
  have hnd : (pre ++ i :: post).Nodup := by rw [← hsplit]; exact p.store.domNodup
  have hnp := List.nodup_append.1 hnd
  have hpre : i ∉ pre := fun hc => hnp.2.2 i hc i (by simp) rfl
  have hpost : i ∉ post := (List.nodup_cons.1 hnp.2.1).1
  refine ⟨pre.flatMap (fun j => match p.store.get j with | none => [] | some a => render j a),
          post.flatMap (fun j => match p.store.get j with | none => [] | some a => render j a),
          ?_, ?_, ?_, ?_⟩
  · show p.store.dom.flatMap _ = _
    rw [hsplit, List.flatMap_append, List.flatMap_cons]
    simp only [hget]
  · show (p.store.set i e' hs).dom.flatMap _ = _
    rw [show (p.store.set i e' hs).dom = p.store.dom from rfl, hsplit,
      List.flatMap_append, List.flatMap_cons]
    rw [flatMap_congr pre _ (fun j => match p.store.get j with | none => [] | some a => render j a)
        (fun j hj => by
          rw [Store.get_set_other p.store i j e' hs (fun hc => hpre (hc ▸ hj))]),
      flatMap_congr post _ (fun j => match p.store.get j with | none => [] | some a => render j a)
        (fun j hj => by
          rw [Store.get_set_other p.store i j e' hs (fun hc => hpost (hc ▸ hj))])]
    simp only [Store.get_set_self]
  · intro l hl
    obtain ⟨j, hj, hlj⟩ := List.mem_flatMap.1 hl
    have hji : j ≠ i := fun hc => hpre (hc ▸ hj)
    cases hgj : p.store.get j with
    | none => rw [hgj] at hlj; simp at hlj
    | some a => rw [hgj] at hlj; rw [render_all_same_id j a l hlj]; exact hji
  · intro l hl
    obtain ⟨j, hj, hlj⟩ := List.mem_flatMap.1 hl
    have hji : j ≠ i := fun hc => hpost (hc ▸ hj)
    cases hgj : p.store.get j with
    | none => rw [hgj] at hlj; simp at hlj
    | some a => rw [hgj] at hlj; rw [render_all_same_id j a l hlj]; exact hji

/-- The ranks a list of lines occupies in one document. -/
def ranksIn (k : DocIx) (ls : List Line) : List Nat :=
  (ls.filter (fun l => l.site.doc == k)).map (fun l => l.site.rank)

/-- The ranks a document's **prose** occupies. -/
def proseRanks (p : PlanCore) (k : DocIx) : List Nat :=
  match p.docs[k]? with
  | none   => []
  | some d => d.prose.map Prod.fst

theorem docRanks_eq (p : PlanCore) (k : DocIx) :
    docRanks p k = proseRanks p k ++ ranksIn k p.lines := rfl

theorem ranksIn_append (k : DocIx) (x y : List Line) :
    ranksIn k (x ++ y) = ranksIn k x ++ ranksIn k y := by
  simp [ranksIn, List.filter_append]

theorem mem_ranksIn {k : DocIx} {ls : List Line} {r : Nat} :
    r ∈ ranksIn k ls ↔ ∃ l, l ∈ ls ∧ l.site.doc = k ∧ l.site.rank = r := by
  unfold ranksIn
  constructor
  · intro h
    obtain ⟨l, hl, hr⟩ := List.mem_map.1 h
    have hf := List.mem_filter.1 hl
    exact ⟨l, hf.1, by simpa using hf.2, hr⟩
  · rintro ⟨l, hl, hd, rfl⟩
    exact List.mem_map.2 ⟨l, List.mem_filter.2 ⟨hl, by simp [hd]⟩, rfl⟩

theorem mem_proseRanks {p : PlanCore} {k : DocIx} {r : Nat} (h : r ∈ proseRanks p k) :
    ∃ d, p.docs[k]? = some d ∧ ∃ q ∈ d.prose, q.1 = r := by
  unfold proseRanks at h
  cases hd : p.docs[k]? with
  | none => rw [hd] at h; simp at h
  | some d =>
      rw [hd] at h
      obtain ⟨q, hq, hr⟩ := List.mem_map.1 h
      exact ⟨d, rfl, q, hq, hr⟩

theorem nodup_of_length_le_one {α : Type} (l : List α) (h : l.length ≤ 1) : l.Nodup := by
  match l with
  | []          => simp
  | [_]         => simp
  | _ :: _ :: _ => simp only [List.length_cons] at h; omega

/-- **One entity puts at most one line in any one document** — the two lines of
a demotion are in two files, which is `wf`.  So the block `lines_set` swaps
contributes at most one rank per document, and `Normalized` never has to
compare it with itself. -/
theorem render_filter_doc_len (i : Id) (e : Entity) (k : DocIx) :
    ((render i e).filter (fun l => l.site.doc == k)).length ≤ 1 := by
  unfold render renderCore
  cases h : e.val.archive with
  | none =>
      simp only
      by_cases hk : e.val.live.doc = k <;> simp [hk]
  | some t =>
      have hne := archive_elsewhere e t.site (Core.archiveSite_some h)
      simp only
      by_cases hk : e.val.live.doc = k
      · have hrk : ¬ (t.site.doc = k) := fun hc => hne (by rw [hc, hk])
        simp [hk, hrk]
      · by_cases hrk : t.site.doc = k <;> simp [hk, hrk]

theorem ranksIn_render_nodup (i : Id) (e : Entity) (k : DocIx) :
    (ranksIn k (render i e)).Nodup := by
  refine nodup_of_length_le_one _ ?_
  unfold ranksIn
  rw [List.length_map]
  exact render_filter_doc_len i e k

/-- Swapping the middle block of a `Nodup` concatenation for a block that is
itself `Nodup` and meets nothing around it. -/
theorem nodup_swap_middle {α : Type} (Pr a b b' c : List α)
    (hold : (Pr ++ (a ++ (b ++ c))).Nodup) (hb' : b'.Nodup)
    (hdis : ∀ r ∈ b', r ∉ Pr ∧ r ∉ a ∧ r ∉ c) :
    (Pr ++ (a ++ (b' ++ c))).Nodup := by
  rw [List.nodup_append] at hold
  obtain ⟨hPr, h1, hd1⟩ := hold
  rw [List.nodup_append] at h1
  obtain ⟨ha, h2, hd2⟩ := h1
  rw [List.nodup_append] at h2
  obtain ⟨_, hc, _⟩ := h2
  refine List.nodup_append.2 ⟨hPr, List.nodup_append.2 ⟨ha,
    List.nodup_append.2 ⟨hb', hc, ?_⟩, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    exact (hdis x hx).2.2 (by rw [hxy]; exact hy)
  · intro x hx y hy hxy
    rcases List.mem_append.1 hy with hy' | hy'
    · exact (hdis y hy').2.1 (by rw [← hxy]; exact hx)
    · exact hd2 x hx y (List.mem_append.2 (Or.inr hy')) hxy
  · intro x hx y hy hxy
    rcases List.mem_append.1 hy with hy' | hy'
    · exact hd1 x hx y (List.mem_append.2 (Or.inl hy')) hxy
    · rcases List.mem_append.1 hy' with hy'' | hy''
      · exact (hdis y hy'').1 (by rw [← hxy]; exact hx)
      · exact hd1 x hx y (List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inr hy'')))) hxy

/-- **The precondition a command owes `Normalized`**, and nothing more: every
line the *new* entity renders sits where nothing else is — no other line of the
plan, and no prose line of that document.  Re-using one of the entity's **own**
sites is allowed, which is what makes `drop` and `est` free of any obligation
at all. -/
def SitesFree (p : PlanCore) (i : Id) (e e' : Entity) : Prop :=
  ∀ l ∈ render i e',
    (∀ m ∈ p.lines, m.site = l.site → m ∈ render i e) ∧
    (∀ d, p.docs[l.site.doc]? = some d → ∀ q ∈ d.prose, q.1 ≠ l.site.rank)

/-- **`Normalized` is preserved by a single-entity update onto free sites** —
the theorem README gap 11 said was not written.  With it, `mapAt`'s decidable
re-check of rank distinctness is an obligation the boundary can *discharge*
rather than a check it merely hopes to pass. -/
theorem normalized_set (p : PlanCore) (i : Id) (e e' : Entity)
    (hs : (p.store.get i).isSome = true) (hget : p.store.get i = some e)
    (hnorm : normalized p = true) (hfree : SitesFree p i e e') :
    normalized { p with store := p.store.set i e' hs } = true := by
  obtain ⟨A, C, hp, hp', hA, hC⟩ := lines_set p i e e' hs hget
  simp only [normalized, List.all_eq_true, decide_eq_true_eq] at hnorm ⊢
  intro k hk
  have hold : (docRanks p k).Nodup := hnorm k hk
  rw [docRanks_eq, hp, ranksIn_append, ranksIn_append] at hold
  show (docRanks { p with store := p.store.set i e' hs } k).Nodup
  rw [docRanks_eq]
  show (proseRanks p k ++ ranksIn k
    (PlanCore.lines { p with store := p.store.set i e' hs })).Nodup
  rw [hp', ranksIn_append, ranksIn_append]
  refine nodup_swap_middle _ _ _ _ _ hold (ranksIn_render_nodup i e' k) ?_
  intro r hr
  obtain ⟨l, hl, hld, hlr⟩ := mem_ranksIn.1 hr
  refine ⟨?_, ?_, ?_⟩
  · intro hcon
    obtain ⟨d, hd, q, hq, hqr⟩ := mem_proseRanks hcon
    exact (hfree l hl).2 d (by rw [hld]; exact hd) q hq (by rw [hqr, hlr])
  · intro hcon
    obtain ⟨m, hm, hmd, hmr⟩ := mem_ranksIn.1 hcon
    have hmem : m ∈ p.lines := by
      rw [hp]; exact List.mem_append.2 (Or.inl hm)
    have := (hfree l hl).1 m hmem (site_eq _ _ (by rw [hmd, hld]) (by rw [hmr, hlr]))
    exact hA m hm (render_all_same_id i e m this)
  · intro hcon
    obtain ⟨m, hm, hmd, hmr⟩ := mem_ranksIn.1 hcon
    have hmem : m ∈ p.lines := by
      rw [hp]
      exact List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inr hm)))
    have := (hfree l hl).1 m hmem (site_eq _ _ (by rw [hmd, hld]) (by rw [hmr, hlr]))
    exact hC m hm (render_all_same_id i e m this)


/-! ## §3.2's derived fields, as functions over the tree

None of these is a stored field, and that is the point: a stored `effective
shape` or a stored `root priority` is a second answer to a question the tree
already answers, which is the shape of S2 and of the `est`/`est_original`
bug. -/

def shapeOf (p : PlanCore) (i : Id) : Shape :=
  match p.store.get i with
  | none   => Shape.none
  | some e => e.val.shape

/-- §3.2's `effective_shape`: "an item with `shape = None` whose **parent** is
an `Interval` is treated as `Point { due: parent.start }` (prep work)."

Note *parent*, not *ancestor*: this is one step and not a closure.  The
transitive version — "the nearest shaped ancestor" — is a different rule that
the spec does not state, and `effectiveShape_does_not_reach_the_grandparent`
below is the theorem that pins down which of the two this is, so nobody has to
read the code to find out. -/
def effectiveShape (p : PlanCore) (i : Id) : Shape :=
  match p.store.get i with
  | none   => Shape.none
  | some e =>
    match e.val.shape with
    | Shape.none =>
      (match e.val.parent with
       | none   => Shape.none
       | some j => match shapeOf p j with
                   | .interval s _ => .point (.dateTime s.day s.time)
                   | _             => Shape.none)
    | s => s

/-- An item that says what it is, is what it says. -/
theorem effectiveShape_as_written (p : PlanCore) (i : Id) (e : Entity)
    (hget : p.store.get i = some e) (h : e.val.shape ≠ Shape.none) :
    effectiveShape p i = e.val.shape := by
  cases hsh : e.val.shape with
  | none         => exact absurd hsh h
  | point d      => simp [effectiveShape, hget, hsh]
  | interval a b => simp [effectiveShape, hget, hsh]
  | window r d   => simp [effectiveShape, hget, hsh]

/-- **§3.2's prep rule.**  The `^x2` of §4.3 — "Midterm review `@x1`" under the
interval `^x1` — is due at the exam's start, and nobody wrote that date down. -/
theorem effectiveShape_prep (p : PlanCore) (i j : Id) (e : Entity) (a b : DT)
    (hget : p.store.get i = some e) (hsh : e.val.shape = Shape.none)
    (hpar : e.val.parent = some j) (hj : shapeOf p j = Shape.interval a b) :
    effectiveShape p i = Shape.point (Moment.dateTime a.day a.time) := by
  simp [effectiveShape, hget, hsh, hpar, hj]

/-- **And it is one step.**  A shapeless child of a shapeless parent has no
shape, whatever the grandparent is — so `effectiveShape` is §3.2's rule and not
a transitive closure someone assumed. -/
theorem effectiveShape_does_not_reach_the_grandparent (p : PlanCore) (i j : Id) (e : Entity)
    (hget : p.store.get i = some e) (hsh : e.val.shape = Shape.none)
    (hpar : e.val.parent = some j) (hj : shapeOf p j = Shape.none) :
    effectiveShape p i = Shape.none := by
  simp [effectiveShape, hget, hsh, hpar, hj]

/-- §3.1's `ci` default: "the parent's, else 3".  A bounded walk up the tree;
`parentsAcyclic` is what says the bound is enough for it to be the real
answer. -/
def effectiveCiAux (p : PlanCore) : Nat → Id → Fin 6
  | 0,     _ => 3
  | n + 1, i =>
    match p.store.get i with
    | none   => 3
    | some e =>
      match e.val.ci with
      | some c => c
      | none   =>
        match e.val.parent with
        | none   => 3
        | some j => effectiveCiAux p n j

def effectiveCi (p : PlanCore) (i : Id) : Fin 6 := effectiveCiAux p (fuel p) i

theorem effectiveCi_explicit (p : PlanCore) (i : Id) (e : Entity) (c : Fin 6)
    (hget : p.store.get i = some e) (hci : e.val.ci = some c) : effectiveCi p i = c := by
  simp [effectiveCi, fuel, effectiveCiAux, hget, hci]

theorem effectiveCi_inherits (p : PlanCore) (n : Nat) (i j : Id) (e : Entity)
    (hget : p.store.get i = some e) (hci : e.val.ci = none) (hpar : e.val.parent = some j) :
    effectiveCiAux p (n + 1) i = effectiveCiAux p n j := by
  simp [effectiveCiAux, hget, hci, hpar]

theorem effectiveCi_default (p : PlanCore) (i : Id) (e : Entity)
    (hget : p.store.get i = some e) (hci : e.val.ci = none) (hpar : e.val.parent = none) :
    effectiveCi p i = 3 := by
  simp [effectiveCi, fuel, effectiveCiAux, hget, hci, hpar]

/-- §3.2's `root_priority`: walk `parent` to the top and read the explicit `!k`
**there**. -/
def rootPrioAux (p : PlanCore) : Nat → Id → Option (Fin 4)
  | 0,     _ => none
  | n + 1, i =>
    match p.store.get i with
    | none   => none
    | some e =>
      match e.val.parent with
      | some j => rootPrioAux p n j
      | none   => e.val.prio

def rootPrio (p : PlanCore) (i : Id) : Option (Fin 4) := rootPrioAux p (fuel p) i

theorem rootPrio_of_a_root (p : PlanCore) (i : Id) (e : Entity)
    (hget : p.store.get i = some e) (hpar : e.val.parent = none) :
    rootPrio p i = e.val.prio := by
  simp [rootPrio, fuel, rootPrioAux, hget, hpar]

/-- **A child's own `!k` is not read** — §4.3's "roots carry explicit
priority", as the fact that the right-hand side does not mention it. -/
theorem rootPrio_walks_past_the_child (p : PlanCore) (n : Nat) (i j : Id) (e : Entity)
    (hget : p.store.get i = some e) (hpar : e.val.parent = some j) :
    rootPrioAux p (n + 1) i = rootPrioAux p n j := by
  simp [rootPrioAux, hget, hpar]

/-! ## What an accepted plan therefore guarantees -/

theorem climb_succ_none (p : PlanCore) (n : Nat) (i : Id) (h : parentStep p i = none) :
    climb p (n + 1) i = i := by simp [climb, h]

theorem climb_succ_some (p : PlanCore) (n : Nat) (i j : Id) (h : parentStep p i = some j) :
    climb p (n + 1) i = climb p n j := by simp [climb, h]

/-- The walk stops because it ran **out of parents**, not because it ran out of
fuel — which is exactly what a bounded iteration has to prove. -/
theorem climb_reaches_a_root (p : PlanCore) : ∀ n i, anc p n i = none →
    parentStep p (climb p n i) = none := by
  intro n
  induction n with
  | zero => intro i h; simp [anc] at h
  | succ m ih =>
      intro i h
      cases hs : parentStep p i with
      | none => rw [climb_succ_none p m i hs]; exact hs
      | some j =>
          rw [climb_succ_some p m i j hs]
          rw [anc_succ_some p m i j hs] at h
          exact ih j h

/-- **§3.2's `root(item)` is total on an accepted plan.** -/
theorem every_item_has_a_root (p : WfPlan) (i : Id) (e : Entity)
    (hget : p.val.store.get i = some e) : parentStep p.val (rootOf p.val i) = none := by
  have hdom : i ∈ p.val.store.dom := (p.val.store.domSpec i).mpr (by rw [hget]; rfl)
  have hacy := (itemsWf_parts p.items).2.2.1
  have hall := List.all_eq_true.1 hacy i hdom
  have hnone : anc p.val (fuel p.val) i = none := by
    simpa [Option.isNone_iff_eq_none] using hall
  exact climb_reaches_a_root p.val _ i hnone

/-- **No item is its own ancestor.**  F5, as a fact about the type. -/
theorem no_item_is_its_own_ancestor (p : WfPlan) (i : Id) (e : Entity)
    (hget : p.val.store.get i = some e) : ¬ OnACycle p.val i := by
  have hdom : i ∈ p.val.store.dom := (p.val.store.domSpec i).mpr (by rw [hget]; rfl)
  exact parentsAcyclic_sound p.val (itemsWf_parts p.items).2.2.1 i hdom

/-- **`@parent` names an item.**  A dangling `@m9` is not a plan. -/
theorem parent_names_an_item (p : WfPlan) (i j : Id) (e : Entity)
    (hget : p.val.store.get i = some e) (hpar : e.val.parent = some j) :
    (p.val.store.get j).isSome = true := by
  have hdom : i ∈ p.val.store.dom := (p.val.store.domSpec i).mpr (by rw [hget]; rfl)
  have hall := List.all_eq_true.1 (itemsWf_parts p.items).2.1 i hdom
  simpa [parentStep, hget, hpar] using hall

/-- **`after:^id` names an item too.** -/
theorem dep_names_an_item (p : WfPlan) (i j : Id) (e : Entity)
    (hget : p.val.store.get i = some e) (hdep : Dep.item j ∈ e.val.after) :
    (p.val.store.get j).isSome = true := by
  have hdom : i ∈ p.val.store.dom := (p.val.store.domSpec i).mpr (by rw [hget]; rfl)
  have hall := List.all_eq_true.1 (itemsWf_parts p.items).2.2.2.1 i hdom
  rw [show depsOf p.val i = depIds e.val.after from by simp [depsOf, hget]] at hall
  refine List.all_eq_true.1 hall j ?_
  simp only [depIds, List.mem_filterMap]
  exact ⟨Dep.item j, hdep, rfl⟩

/-- **No set of items can all be waiting on each other.**  §5.5's cycle error,
except that the cyclic plan is not a value. -/
theorem no_deadlocked_set (p : WfPlan) (c : List Id)
    (hc : ∀ x ∈ c, x ∈ p.val.store.dom) : ¬ Deadlocked p.val c :=
  afterAcyclic_sound p.val (itemsWf_parts p.items).2.2.2.2.1 c hc

/-- §4.2: a `# Demoted` section is a month-file section (§6.3), wherever it is
written. -/
theorem a_demoted_section_is_a_month_section (p : WfPlan) (d : Doc) (hd : d ∈ p.val.docs)
    (q : Nat × List Char) (hq : q ∈ d.prose) (hh : isHeading q.2 = true)
    (hk : secKind q.2 = SecKind.demoted) : docKind d = DocKind.month := by
  have hsec := (itemsWf_parts p.items).2.2.2.2.2.1
  simp only [sectionsWf, Bool.and_eq_true] at hsec
  have h1 := List.all_eq_true.1 hsec.1 d hd
  have h2 := List.all_eq_true.1 h1 q hq
  simp only [hh, if_true, hk, beq_iff_eq] at h2
  exact h2

/-- §4.2: and a `# Pinned` section is a day-file section (§6.2). -/
theorem a_pinned_section_is_a_day_section (p : WfPlan) (d : Doc) (hd : d ∈ p.val.docs)
    (q : Nat × List Char) (hq : q ∈ d.prose) (hh : isHeading q.2 = true)
    (hk : secKind q.2 = SecKind.pinned) : docKind d = DocKind.day := by
  have hsec := (itemsWf_parts p.items).2.2.2.2.2.1
  simp only [sectionsWf, Bool.and_eq_true] at hsec
  have h1 := List.all_eq_true.1 hsec.1 d hd
  have h2 := List.all_eq_true.1 h1 q hq
  simp only [hh, if_true, hk, beq_iff_eq] at h2
  exact h2

/-- §4.3's day file: the item lines it holds are the `# Pinned` ones.  The
generated plan block, `## Log` and `## Notes` are prose, and an item line
underneath any of them is not a plan. -/
theorem a_day_file_holds_only_pinned_items (p : WfPlan) (i : Id) (e : Entity)
    (hget : p.val.store.get i = some e)
    (hday : docKindAt p.val e.val.live.doc = DocKind.day) :
    sectionKindAt p.val e.val.live = some SecKind.pinned := by
  have hdom : i ∈ p.val.store.dom := (p.val.store.domSpec i).mpr (by rw [hget]; rfl)
  have hsec := (itemsWf_parts p.items).2.2.2.2.2.1
  simp only [sectionsWf, Bool.and_eq_true] at hsec
  have h1 := List.all_eq_true.1 hsec.2 i hdom
  rw [hget] at h1
  simp only [Bool.and_eq_true] at h1
  have h2 := h1.1
  simp only [placementSectionWf, hday] at h2
  cases hsk : sectionKindAt p.val e.val.live with
  | none => rw [hsk] at h2; simp at h2
  | some k =>
      cases k with
      | pinned => rfl
      | demoted => rw [hsk] at h2; simp at h2
      | series n => rw [hsk] at h2; simp at h2
      | organisational => rw [hsk] at h2; simp at h2

theorem shapeWf_of_mem (p : WfPlan) (i : Id) (e : Entity) (hget : p.val.store.get i = some e) :
    shapeWfFor (docKindAt p.val e.val.live.doc) e.val = true := by
  have hdom : i ∈ p.val.store.dom := (p.val.store.domSpec i).mpr (by rw [hget]; rfl)
  have hall := List.all_eq_true.1 (itemsWf_parts p.items).2.2.2.2.2.2 i hdom
  rw [hget] at hall
  exact hall

/-- §6.2: "month items are outcomes, not work" — an outcome carries no date. -/
theorem month_items_are_outcomes (p : WfPlan) (i : Id) (e : Entity)
    (hget : p.val.store.get i = some e)
    (hm : docKindAt p.val e.val.live.doc = DocKind.month) : e.val.shape = Shape.none := by
  have h := shapeWf_of_mem p i e hget
  rw [hm] at h
  simpa [shapeWfFor] using h

/-- §4.3's `calendar/`: "generated intervals". -/
theorem calendar_lines_are_intervals (p : WfPlan) (i : Id) (e : Entity)
    (hget : p.val.store.get i = some e)
    (hc : docKindAt p.val e.val.live.doc = DocKind.calendar) :
    ∃ a b, e.val.shape = Shape.interval a b := by
  have h := shapeWf_of_mem p i e hget
  rw [hc] at h
  simp only [shapeWfFor] at h
  cases hsh : e.val.shape with
  | interval a b => exact ⟨a, b, rfl⟩
  | none         => rw [hsh] at h; simp at h
  | point d      => rw [hsh] at h; simp at h
  | window r d   => rw [hsh] at h; simp at h

/-- §4.3's `routines.md`: "every line is `open`, has a window or
`after-done`". -/
theorem routine_lines_are_open (p : WfPlan) (i : Id) (e : Entity)
    (hget : p.val.store.get i = some e)
    (hr : docKindAt p.val e.val.live.doc = DocKind.routines) :
    e.val.scope = Scope.openEnded := by
  have h := shapeWf_of_mem p i e hget
  rw [hr] at h
  simp only [shapeWfFor, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem routine_lines_have_a_window_or_after_done (p : WfPlan) (i : Id) (e : Entity)
    (hget : p.val.store.get i = some e)
    (hr : docKindAt p.val e.val.live.doc = DocKind.routines) :
    (∃ r d, e.val.shape = Shape.window r d) ∨ (∃ a, e.val.recur = Recur.afterDone a) := by
  have h := shapeWf_of_mem p i e hget
  rw [hr] at h
  simp only [shapeWfFor, Bool.and_eq_true] at h
  have h2 := h.2
  cases hsh : e.val.shape with
  | window r d => exact Or.inl ⟨r, d, rfl⟩
  | none =>
      rw [hsh] at h2
      cases hrc : e.val.recur with
      | afterDone a => exact Or.inr ⟨a, rfl⟩
      | none => rw [hrc] at h2; simp at h2
      | calendar r => rw [hrc] at h2; simp at h2
      | onEvent ev => rw [hrc] at h2; simp at h2
  | point d =>
      rw [hsh] at h2
      cases hrc : e.val.recur with
      | afterDone a => exact Or.inr ⟨a, rfl⟩
      | none => rw [hrc] at h2; simp at h2
      | calendar r => rw [hrc] at h2; simp at h2
      | onEvent ev => rw [hrc] at h2; simp at h2
  | interval a b =>
      rw [hsh] at h2
      cases hrc : e.val.recur with
      | afterDone a => exact Or.inr ⟨a, rfl⟩
      | none => rw [hrc] at h2; simp at h2
      | calendar r => rw [hrc] at h2; simp at h2
      | onEvent ev => rw [hrc] at h2; simp at h2

/-- §4.3's `optional.md`: `open`, and it says how long it takes — the planner
gives it a rest slot, and a rest slot has a length. -/
theorem optional_items_declare_a_duration (p : WfPlan) (i : Id) (e : Entity)
    (hget : p.val.store.get i = some e)
    (ho : docKindAt p.val e.val.live.doc = DocKind.optional) :
    e.val.scope = Scope.openEnded ∧ ∃ dv, declaredDur e.val = some dv ∧ durPositive dv = true := by
  have h := shapeWf_of_mem p i e hget
  rw [ho] at h
  simp only [shapeWfFor, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  cases hd : declaredDur e.val with
  | none => rw [hd] at h2; simp at h2
  | some dv => rw [hd] at h2; exact ⟨dv, rfl, h2⟩


/-- **And no prose line hides under an item line.**  `weave` orders a document
by rank and breaks a tie in favour of prose, so a prose entry sharing a rank
with an item line would move that item — a change to the file with no command
run.  `Normalized` counts prose ranks and item ranks in one list, so the tie
cannot arise. -/
theorem no_prose_line_shares_a_rank (p : WfPlan) (l : Line) (hl : l ∈ p.val.lines)
    (d : Doc) (hd : p.val.docs[l.site.doc]? = some d)
    (q : Nat × List Char) (hq : q ∈ d.prose) : q.1 ≠ l.site.rank := by
  have hk : l.site.doc < p.val.docs.length := no_line_is_lost p l hl
  have hnorm := (itemsWf_parts p.items).1
  simp only [normalized, List.all_eq_true] at hnorm
  have hnd : (docRanks p.val l.site.doc).Nodup := by
    have := hnorm l.site.doc (List.mem_range.2 hk)
    simpa using this
  rw [show docRanks p.val l.site.doc
        = (d.prose.map Prod.fst) ++
          ((p.val.lines.filter (fun x => x.site.doc == l.site.doc)).map (fun x => x.site.rank))
      from by simp [docRanks, hd]] at hnd
  have hdis := (List.nodup_append.1 hnd).2.2
  refine hdis q.1 (List.mem_map.2 ⟨q, hq, rfl⟩) l.site.rank ?_
  exact List.mem_map.2 ⟨l, by simp [List.mem_filter, hl], rfl⟩


/-! ### And the file-kind checks bite

A checker that no input can fail is not a checker.  These are the two witnesses
that the §4.3 rules refuse something: a calendar line that is not an interval,
and a day-file item outside `# Pinned`.  Neither is a plan. -/

theorem a_shapeless_calendar_line_is_rejected (p : PlanCore) (i : Id) (e : Entity)
    (hdom : i ∈ p.store.dom) (hget : p.store.get i = some e)
    (hc : docKindAt p e.val.live.doc = DocKind.calendar) (hsh : e.val.shape = Shape.none) :
    shapesWf p = false := by
  cases hb : shapesWf p with
  | false => rfl
  | true =>
      have hall := List.all_eq_true.1 hb i hdom
      rw [hget] at hall
      simp [hc, shapeWfFor, hsh] at hall

theorem an_unpinned_day_item_is_rejected (p : PlanCore) (i : Id) (e : Entity)
    (hdom : i ∈ p.store.dom) (hget : p.store.get i = some e)
    (hday : docKindAt p e.val.live.doc = DocKind.day)
    (hsec : sectionKindAt p e.val.live = none) : sectionsWf p = false := by
  cases hb : sectionsWf p with
  | false => rfl
  | true =>
      simp only [sectionsWf, Bool.and_eq_true] at hb
      have hall := List.all_eq_true.1 hb.2 i hdom
      rw [hget] at hall
      simp only [Bool.and_eq_true] at hall
      have h2 := hall.1
      simp [placementSectionWf, hday, hsec] at h2

end Tm
