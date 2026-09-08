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

/-- The observable content of one entity.  `line` is the verbatim token vector
(§4.2): the semantic fields are views of it, so there is one place an estimate
can live. -/
structure Core where
  live      : Site
  archive   : Option Site      -- at most one tombstone a close left behind
  status    : Status
  line      : RawItem
  stamps    : List Nat         -- `demoted:` periods, newest last
deriving DecidableEq, Repr

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
    glyphAt ⟨site, none, s, l, st⟩ site = g := by
  cases g <;> simp only [statusOfGlyph, Option.some.injEq, reduceCtorEq] at h <;>
    first | (subst h; rfl) | rfl

/-- **Fidelity, paired.**  Same, for the two-line form a demotion leaves: the
live site renders the glyph it was read with, and the tombstone renders `[-]`
(`archive_line_is_demoted`). -/
theorem glyphAt_statusOfGlyphDemoted {g : Glyph} {s : Status}
    (h : statusOfGlyphDemoted g = some s) (live arch : Site) (hne : arch ≠ live)
    (l : RawItem) (st : List Nat) :
    glyphAt ⟨live, some arch, s, l, st⟩ live = g := by
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
