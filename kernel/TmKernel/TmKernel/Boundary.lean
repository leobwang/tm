import TmKernel.Cmd
import Lean.Data.Json
/-!
# The boundary: `String → String`, and nothing else

The parser and the serializer are in the kernel, so **nothing is marshalled**:
the UI hands over the raw text of every file and gets raw text back.  One
`@[export]`, one shim function, and adding a command is one case in `dispatch`.

Two rules from the FFI spike, both applied here:

* **Every bounded type gets a smart constructor used by its decoder.**  A plain
  `structure Horizon where depth : Nat` accepted `horizon: 99`; `Fin 3` plus
  `Grain.ofNat?` rejects it.
* **`Except` all the way through; `.toOption` is banned.**  `.toOption` is how
  the spike silently turned `est: -3` into `est: null`, reproducing tm's own
  estimate-loss bug inside the verified kernel's boundary code.
-/
namespace Tm
open Lean

def grainCount : Nat := 3

/-- The only way in for a grain.  Rust cannot fabricate a `Fin 3`. -/
def Grain.ofNat? (n : Nat) : Option Grain :=
  if h : n < grainCount then some ⟨n, h⟩ else none

theorem grain_rejects_out_of_range : Grain.ofNat? 3 = none := by decide
theorem grain_rejects_99 : Grain.ofNat? 99 = none := by decide
theorem grain_accepts_month : Grain.ofNat? 2 = some month := by decide

/-! ## Building a plan from text -/

def emptyStore : Store where
  get := fun _ => none
  dom := []
  domSpec := by intro i; simp
  domNodup := by simp

def Store.insert (s : Store) (i : Id) (e : Entity) : Store :=
  if h : i ∈ s.dom then
    { get := fun j => if j = i then some e else s.get j
      dom := s.dom
      domSpec := by
        intro j
        by_cases hj : j = i
        · subst hj; simp [h]
        · simp only [hj, if_false]; exact s.domSpec j
      domNodup := s.domNodup }
  else
    { get := fun j => if j = i then some e else s.get j
      dom := i :: s.dom
      domSpec := by
        intro j
        by_cases hj : j = i
        · subst hj; simp
        · simp only [List.mem_cons, hj, false_or, if_false]; exact s.domSpec j
      domNodup := by simp [List.nodup_cons, h, s.domNodup] }

/-- Load errors are the diagnostics `tm check` prints.  Acceptance is exactly
"`load` returned `.ok`", so the checker cannot be weaker than the invariant. -/
inductive LErr
  /-- more lines of one id than any entity can render, or two in one file -/
  | dupId (i : Id)
  /-- a `[-]` with no partner.  A demotion is two lines, one of them the
      tombstone; a single `[-]` is not a state this kernel can hold, and the
      first version of the loader turned it into a live `[ ]` item. -/
  | orphanDemotion (i : Id)
  /-- two lines of one id whose bytes differ.  An entity owns one token vector,
      so there is no value that renders both. -/
  | splitLine (i : Id)
  /-- two lines of one id, in two files, with the same bytes, whose boxes are
      not a demotion: `render` writes a second line only as a tombstone, and a
      tombstone is `[-]`.  Nothing renders these two, so they are rejected
      rather than approximated. -/
  | notADemotion (i : Id)
  /-- two lines of one id in two documents whose **horizons do not order them**,
      so nothing in the files says which line is the tombstone.  `demote` writes
      `[-]` at both sites, so the boxes cannot settle it either; the closed file
      is the one behind the other in `horizonPrecedes`, and if the request
      declared no region for one of them, or the same region for both, that
      question has no answer.  It is asked here rather than answered by the order
      the host happened to list the documents. -/
  | ambiguousDemotion (i : Id)
  /-- a line that looks like an item and does not parse -/
  | badLine (path : List Char) (n : Nat) (why : PErr)
  /-- two documents with one path: they are one file on disk -/
  | duplicatePath (path : List Char)
deriving Repr

/-! ### Rejection is real

A line that *looks* like an item and does not parse used to be silently
reclassified as prose: `- [Z] x ^a1` and `- [ ] two ^a1 ^a2` were accepted, kept
and written back, and `LErr.badLine` was dead code.  "Accept or reject" is the
whole contract of a boundary, so the scan below is run before anything is
built, and only `PErr.notAnItem` — the line does not have an item's shape at
all — counts as prose. -/

def scanLines (path : List Char) : Nat → List (List Char) → Except LErr Unit
  | _, []      => .ok ()
  | k, l :: rest =>
    match parseItem l with
    | .ok _             => scanLines path (k + 1) rest
    | .error .notAnItem => scanLines path (k + 1) rest
    | .error e          => .error (.badLine path k e)

/-- What acceptance buys: every prose line of an accepted document failed to
parse **because it is not an item line**, not because it is a broken one. -/
theorem scanLines_prose (path : List Char) (k : Nat) (ls : List (List Char))
    (h : scanLines path k ls = .ok ()) :
    ∀ q ∈ (splitDoc k ls).prose, parseItem q.2 = .error .notAnItem := by
  induction ls generalizing k with
  | nil => intro q hq; simp [splitDoc] at hq
  | cons l rest ih =>
      intro q hq
      unfold splitDoc at hq
      simp only at hq
      unfold scanLines at h
      cases hpl : parseItem l with
      | ok trip =>
          rw [hpl] at hq h
          simp only at h
          exact ih (k + 1) h q hq
      | error e =>
          cases e with
          | notAnItem =>
              rw [hpl] at hq h
              simp only at h
              simp only [List.mem_cons] at hq
              rcases hq with rfl | hq
              · exact hpl
              · exact ih (k + 1) h q hq
          | badState c => rw [hpl] at h; simp at h
          | noId       => rw [hpl] at h; simp at h
          | manyIds    => rw [hpl] at h; simp at h

/-! ### The loader is the inverse of `render`, and where the inverse is not
unique it rejects

`render` writes at most two lines for an id: the live one, whose box is
`glyphAt` of the status, and the tombstone, whose box is always `[-]`.  So the
loader must group a document set's item lines **by id** and invert that.  The
first version mapped each line to its own entity with `archive = none` and sent
`[-]` to `live free`, which `glyphAt` renders as `[ ]`: a demotion record turned
into an open task with no command run.  It also meant the kernel could not read
back the two-line form its own `demote` writes.

The promise this section keeps, stated exactly, because a weaker version of it
was false here:

* where **no** entity renders the lines it was given, the loader returns an
  `LErr` and never picks a nearby state;
* where **more than one** entity renders them, the loader does not pick either.
  It asks the documents which line is the tombstone, and if they do not say, it
  returns `LErr.ambiguousDemotion`.

The second clause is not hypothetical: it is the whole two-line demotion form.
`demote` renders `[-]` at *both* sites, so both orientations of a `[-]`/`[-]`
pair are entities that render exactly those two lines, and a loader that tries
one and then the other resolves a real ambiguity by argument order — which is
the order the host listed the files in.  Swapping two documents in the request
then moved which file a `drop` marked.

What breaks the tie is the domain, not the argument order: the tombstone stays
in the horizon that was **closed** and the live line goes to the one the close
filed into, which is strictly after it (`demotion_target_follows_the_closed_region`,
Grain.lean).  So a `Placement` carries its document's horizon, `orientPair` is a
function of the pair and not of its order (`orientPair_comm`), and
`demotionsOriented` (Plan.lean) makes "the tombstone is behind the live line" a
fact about every accepted plan, so no command can write a pair the loader would
then have to guess at. -/

structure Placement where
  doc    : DocIx
  rank   : Nat
  id     : Id
  glyph  : Glyph
  item   : RawItem
  /-- the horizon of the document this line was read from; `none` is backlog -/
  region : Option Region
deriving DecidableEq, Repr, Inhabited

def placementsOfDoc (k : DocIx) (reg : Option Region) (d : DocSplit) : List Placement :=
  d.items.map (fun p => ⟨k, p.1, p.2.1, p.2.2.1, p.2.2.2, reg⟩)

def dedupIds : List Id → List Id
  | []        => []
  | i :: rest => if i ∈ dedupIds rest then dedupIds rest else i :: dedupIds rest

theorem dedupIds_cons (i : Id) (t : List Id) :
    dedupIds (i :: t) = if i ∈ dedupIds t then dedupIds t else i :: dedupIds t := rfl

theorem mem_dedupIds (l : List Id) (i : Id) : i ∈ dedupIds l ↔ i ∈ l := by
  induction l with
  | nil => simp [dedupIds]
  | cons a t ih =>
      rw [dedupIds_cons]
      by_cases h : a ∈ dedupIds t
      · rw [if_pos h]
        constructor
        · intro hm; exact List.mem_cons.2 (Or.inr (ih.1 hm))
        · intro hm
          rcases List.mem_cons.1 hm with rfl | hm'
          · exact h
          · exact ih.2 hm'
      · rw [if_neg h]
        simp only [List.mem_cons, ih]

theorem dedupIds_nodup (l : List Id) : (dedupIds l).Nodup := by
  induction l with
  | nil => simp [dedupIds]
  | cons a t ih =>
      rw [dedupIds_cons]
      by_cases h : a ∈ dedupIds t
      · rw [if_pos h]; exact ih
      · rw [if_neg h]; exact List.nodup_cons.2 ⟨h, ih⟩

/-- Build the entity whose live line is `live` and whose tombstone is `arch`.
`none` means no entity renders that pair — the caller rejects. -/
def pairEntity (arch live : Placement) : Option Entity :=
  match arch.glyph with
  | .demoted =>
    match statusOfGlyphDemoted live.glyph with
    | none    => none
    | some st =>
      if h : wf ({ live := ⟨live.doc, live.rank⟩, archive := some ⟨arch.doc, arch.rank⟩,
                   status := st, line := live.item, stamps := [] } : Core) = true
      then some ⟨_, h⟩ else none
  | _ => none

/-- One line on its own: the entity that renders exactly it. -/
def loneEntity (i : Id) (q : Placement) : Except LErr Entity :=
  match statusOfGlyph q.glyph with
  | some st => .ok ⟨{ live := ⟨q.doc, q.rank⟩, archive := none, status := st,
                      line := q.item, stamps := [] }, rfl⟩
  | none    => .error (.orphanDemotion i)

/-- **Which line is the tombstone, decided by the files.**  The closed horizon
comes first; `horizonPrecedes` is antisymmetric, so at most one of the two
orientations is a demotion and the answer does not depend on which line was
listed first.  `none` — the two documents declare no order — is the ambiguity,
and it is reported rather than resolved. -/
def orientPair (a b : Placement) : Option (Placement × Placement) :=
  if horizonPrecedes a.region b.region then some (a, b)
  else if horizonPrecedes b.region a.region then some (b, a)
  else none

/-- **The loader's answer is a function of the two lines, not of their order.**
This is the defect this section exists to remove, as a theorem. -/
theorem orientPair_comm (a b : Placement) : orientPair a b = orientPair b a := by
  unfold orientPair
  by_cases hab : horizonPrecedes a.region b.region = true
  · rw [if_pos hab, if_neg (by simp [horizonPrecedes_asymm hab]), if_pos hab]
  · simp only [Bool.not_eq_true] at hab
    by_cases hba : horizonPrecedes b.region a.region = true
    · rw [if_neg (by simp [hab]), if_pos hba, if_pos hba]
    · simp only [Bool.not_eq_true] at hba
      rw [if_neg (by simp [hab]), if_neg (by simp [hba]), if_neg (by simp [hba]),
        if_neg (by simp [hab])]

theorem orientPair_cases {a b arch live : Placement} (h : orientPair a b = some (arch, live)) :
    ((arch = a ∧ live = b) ∨ (arch = b ∧ live = a)) ∧
      horizonPrecedes arch.region live.region = true := by
  unfold orientPair at h
  split at h
  · rename_i hab
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    exact ⟨Or.inl ⟨rfl, rfl⟩, hab⟩
  · split at h
    · rename_i hba
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2
      exact ⟨Or.inr ⟨rfl, rfl⟩, hba⟩
    · simp at h

/-- Two lines of one id: the only entity that renders both is a half-finished
demotion, and *which* half-finished demotion is settled by the two documents'
horizons before any glyph is looked at.  Anything else is rejected — including
the two lines in one file, which is the invariant itself, and the pair whose
horizons do not order it, which is the one the previous version silently
resolved by argument order. -/
def pairedEntity (i : Id) (a b : Placement) : Except LErr Entity :=
  if a.doc == b.doc then .error (.dupId i)
  else if a.item != b.item then .error (.splitLine i)
  else
    match orientPair a b with
    | none => .error (.ambiguousDemotion i)
    | some (arch, live) =>
      match pairEntity arch live with
      | some e => .ok e
      | none   => .error (.notADemotion i)

/-- **The whole defect, refuted.**  Listing the two documents the other way
round is the same request: the loader's answer — the entity, or the named error
— does not move. -/
theorem pairedEntity_order_independent (i : Id) (a b : Placement) :
    pairedEntity i a b = pairedEntity i b a := by
  have hdoc : (b.doc == a.doc) = (a.doc == b.doc) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact eq_comm
  have hitem : (b.item != a.item) = (a.item != b.item) := by
    rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]; exact ne_comm
  unfold pairedEntity
  rw [hdoc, hitem, orientPair_comm b a]

/-- **The ambiguity is named, not resolved.**  Two lines of one id whose
documents declare no order between them — two backlog files, one file with no
declared region, two files claiming the same week — are rejected by name.  The
`[-]`/`[-]` pair this is really about is the one `demote` writes, and the
kernel's own output can never be in this state: `demotionsOriented` is part of
`planWf`, so `mapAt` refuses to produce it (`mapAt_rejects_unoriented`). -/
theorem unordered_horizons_are_rejected (i : Id) (a b : Placement)
    (hd : a.doc ≠ b.doc) (hi : a.item = b.item)
    (hab : horizonPrecedes a.region b.region = false)
    (hba : horizonPrecedes b.region a.region = false) :
    pairedEntity i a b = .error (.ambiguousDemotion i) := by
  unfold pairedEntity orientPair
  rw [if_neg (by simpa using hd), if_neg (by simp [hi]), if_neg (by simp [hab]),
    if_neg (by simp [hba])]

/-- The whole inverse, for one id's lines. -/
def buildEntity (i : Id) : List Placement → Except LErr Entity
  | [q]    => loneEntity i q
  | [a, b] => pairedEntity i a b
  | _      => .error (.dupId i)

def buildEntities (ps : List Placement) : Except LErr (List (Id × Entity)) :=
  (dedupIds (ps.map Placement.id)).foldlM
    (fun acc i => do
      let e ← buildEntity i (ps.filter (fun q => q.id == i))
      pure (acc ++ [(i, e)]))
    []

def loadStore (items : List (Id × Entity)) : Store :=
  items.foldl (fun s p => s.insert p.1 p.2) emptyStore

/-! ### Fidelity: what the loader builds renders the line it was read from

`serialize_parse` (Line.lean) is a theorem about the glyph the **parser
returned**, and the pipeline discards that glyph and asks `glyphAt` for a new
one.  The `[-]` bug lived in exactly that gap: `serialize_parse` stayed true
while a `[-]` line came back `[ ]`.  These close it — they are stated about the
entity the loader builds, which is what the FFI renders from. -/

theorem lone_placement_renders_back (i : Id) (q : Placement) (e : Entity)
    (he : loneEntity i q = .ok e) :
    e.val.live = ⟨q.doc, q.rank⟩ ∧ e.val.line = q.item ∧
      glyphAt e.val e.val.live = q.glyph := by
  unfold loneEntity at he
  split at he
  · rename_i st hst
    injection he with he
    subst he
    exact ⟨rfl, rfl, glyphAt_statusOfGlyph hst _ _ _⟩
  · simp at he

theorem pairEntity_renders_back (arch live : Placement) (e : Entity)
    (h : pairEntity arch live = some e) :
    e.val.live = ⟨live.doc, live.rank⟩ ∧ e.val.archive = some ⟨arch.doc, arch.rank⟩ ∧
      e.val.line = live.item ∧ arch.glyph = Glyph.demoted ∧
      glyphAt e.val e.val.live = live.glyph ∧
      glyphAt e.val ⟨arch.doc, arch.rank⟩ = Glyph.demoted := by
  unfold pairEntity at h
  split at h
  · rename_i harch
    split at h
    · simp at h
    · rename_i st hst
      split at h
      · rename_i hwf
        injection h with h
        subst h
        have hne : (⟨arch.doc, arch.rank⟩ : Site) ≠ ⟨live.doc, live.rank⟩ := by
          intro hc
          simp only [wf, wfPair, bne_iff_ne, ne_eq] at hwf
          exact hwf (congrArg Site.doc hc)
        exact ⟨rfl, rfl, rfl, harch,
          glyphAt_statusOfGlyphDemoted hst _ _ hne _ _,
          archive_line_is_demoted _ _ rfl⟩
      · simp at h
  · simp at h

/-- **The two-line form a `demote` writes is read back as the entity that wrote
it, and there is exactly one such entity.**  Both boxes come back as they were
found, so the kernel can round-trip its own output — which the first version
could not: it rejected two lines of one id outright.

The orientation is `orientPair a b`, a function of the two lines that is
symmetric in them (`orientPair_comm`), so this conclusion is determinate: the
tombstone is the line in the closed horizon, whichever order the host listed the
documents in.  The previous statement of this theorem was a disjunction over the
two orientations, which is what an honest theorem about a loader that picked one
by argument order had to look like. -/
theorem paired_placement_renders_back (i : Id) (a b : Placement) (e : Entity)
    (he : pairedEntity i a b = .ok e) :
    ∃ arch live : Placement,
      orientPair a b = some (arch, live) ∧
      horizonPrecedes arch.region live.region = true ∧
      e.val.live = ⟨live.doc, live.rank⟩ ∧ e.val.archive = some ⟨arch.doc, arch.rank⟩ ∧
      e.val.line = live.item ∧ a.item = b.item ∧ arch.glyph = Glyph.demoted ∧
      glyphAt e.val e.val.live = live.glyph ∧
      glyphAt e.val ⟨arch.doc, arch.rank⟩ = Glyph.demoted := by
  unfold pairedEntity at he
  split at he
  · simp at he
  · split at he
    · simp at he
    · rename_i hitem
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hitem
      split at he
      · simp at he
      · rename_i arch live hor
        split at he
        · rename_i x hx
          injection he with he
          subst he
          obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pairEntity_renders_back arch live x hx
          exact ⟨arch, live, hor, (orientPair_cases hor).2, h1, h2, h3, hitem, h4, h5, h6⟩
        · simp at he

/-- **The line round trip through the pipeline the FFI actually runs**, for a
line the loader takes on its own.  Parse the bytes, build the entity, ask
`glyphAt` for the box, serialise: the same bytes.  The `[-]` regression is a
counterexample to this statement and not to `serialize_parse`, which is why it
survived. -/
theorem load_render_line (cs : List Char) (i : Id) (g : Glyph) (r : RawItem)
    (k rk : Nat) (reg : Option Region) (e : Entity) (hp : parseItem cs = .ok (i, g, r))
    (he : loneEntity i ⟨k, rk, i, g, r, reg⟩ = .ok e) :
    serializeItem i (glyphAt e.val e.val.live) e.val.line = cs := by
  obtain ⟨_, hline, hglyph⟩ := lone_placement_renders_back i ⟨k, rk, i, g, r, reg⟩ e he
  rw [hglyph, hline]
  exact serialize_parse cs i g r hp

/-- **Both lines of a demotion come back as they were found.**  Whichever of
the two the loader made the tombstone, each site renders the box that was in the
file at that site and the bytes are the entity's one token vector — so with
`serialize_parse` each line is byte-identical to its input.  The first version
of the loader could not even *load* this shape: two lines of one id were
rejected outright, so the kernel could not read its own `demote` output. -/
theorem paired_renders_each_placement (i : Id) (a b : Placement) (e : Entity)
    (he : pairedEntity i a b = .ok e) :
    glyphAt e.val ⟨a.doc, a.rank⟩ = a.glyph ∧ glyphAt e.val ⟨b.doc, b.rank⟩ = b.glyph ∧
      e.val.line = a.item ∧ e.val.line = b.item := by
  obtain ⟨arch, live, hor0, _, hlive, _, hln, hitem, hag, hg, hd⟩ :=
    paired_placement_renders_back i a b e he
  have hor := (orientPair_cases hor0).1
  rcases hor with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · subst ha; subst hb
    refine ⟨by rw [hd, hag], ?_, ?_, hln⟩
    · rw [← hlive] at *; exact hg
    · rw [hln, hitem]
  · subst ha; subst hb
    refine ⟨?_, by rw [hd, hag], hln, ?_⟩
    · rw [← hlive] at *; exact hg
    · rw [hln, ← hitem]

/-! ## Rendering a plan back to text -/

def insertByRank (x : Nat × List Char) : List (Nat × List Char) → List (Nat × List Char)
  | []      => [x]
  | y :: ys => if x.1 ≤ y.1 then x :: y :: ys else y :: insertByRank x ys

def sortByRank (l : List (Nat × List Char)) : List (Nat × List Char) :=
  l.foldr insertByRank []

def renderDocAt (p : PlanCore) (k : DocIx) (d : Doc) : List (List Char) :=
  weave (sortByRank d.prose)
    (sortByRank ((p.lines.filter (fun l => l.site.doc == k)).map
      (fun l => (l.site.rank, l.text))))

/-! ### `sortByRank` is a reconstruction, not a choice

`renderDocAt` takes the store's lines for one document — in whatever order the
store enumerated its domain — and puts them back in rank order.  For that to be
the *inverse* of `splitDoc` rather than a second opinion about it, three things
have to be true of the sort, and all three are proved here: it leaves an
already-ordered list alone, it moves nothing in or out, and it does not merge
two ranks.  Together with rank distinctness (`Normalized`, part of `planWf`)
the sorted list is then **determined by its members** (`sorted_ext_by_key`,
Plan.lean) — so the bytes a host gets back do not depend on the order the store
enumerated, which is the same defect `orientPair_comm` removes for the demotion
pair. -/

theorem sortByRank_nil : sortByRank [] = [] := rfl

theorem sortByRank_cons (x : Nat × List Char) (xs : List (Nat × List Char)) :
    sortByRank (x :: xs) = insertByRank x (sortByRank xs) := rfl

/-- Insertion moves nothing in and nothing out. -/
theorem insertByRank_mem (x y : Nat × List Char) : ∀ l : List (Nat × List Char),
    y ∈ insertByRank x l ↔ (y = x ∨ y ∈ l) := by
  intro l
  induction l with
  | nil => simp [insertByRank]
  | cons z zs ih =>
      rw [insertByRank]
      by_cases h : x.1 ≤ z.1
      · simp [h]
      · simp only [h, if_false, List.mem_cons, ih]
        constructor
        · intro hh
          rcases hh with hh | hh | hh
          · exact Or.inr (Or.inl hh)
          · exact Or.inl hh
          · exact Or.inr (Or.inr hh)
        · intro hh
          rcases hh with hh | hh | hh
          · exact Or.inr (Or.inl hh)
          · exact Or.inl hh
          · exact Or.inr (Or.inr hh)

theorem sortByRank_mem (y : Nat × List Char) : ∀ l : List (Nat × List Char),
    y ∈ sortByRank l ↔ y ∈ l := by
  intro l
  induction l with
  | nil => simp [sortByRank_nil]
  | cons x xs ih => rw [sortByRank_cons, insertByRank_mem, ih, List.mem_cons]

/-- Insertion into a rank-ordered list is rank-ordered. -/
theorem insertByRank_sorted (x : Nat × List Char) : ∀ l : List (Nat × List Char),
    l.Pairwise (fun a b => a.1 ≤ b.1) → (insertByRank x l).Pairwise (fun a b => a.1 ≤ b.1) := by
  intro l
  induction l with
  | nil => intro _; simp [insertByRank]
  | cons z zs ih =>
      intro h
      rw [List.pairwise_cons] at h
      rw [insertByRank]
      by_cases hx : x.1 ≤ z.1
      · rw [if_pos hx]
        refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 h⟩
        intro b hb
        rcases List.mem_cons.1 hb with hb' | hb'
        · rw [hb']; exact hx
        · exact Nat.le_trans hx (h.1 b hb')
      · rw [if_neg hx]
        refine List.pairwise_cons.2 ⟨?_, ih h.2⟩
        intro b hb
        rcases (insertByRank_mem x b zs).1 hb with hb' | hb'
        · rw [hb']; omega
        · exact h.1 b hb'

theorem sortByRank_sorted : ∀ l : List (Nat × List Char),
    (sortByRank l).Pairwise (fun a b => a.1 ≤ b.1) := by
  intro l
  induction l with
  | nil => simp [sortByRank_nil]
  | cons x xs ih => rw [sortByRank_cons]; exact insertByRank_sorted x _ ih

/-- Insertion of a fresh rank into a list of distinct ranks keeps them
distinct — the half of the argument `Normalized` supplies. -/
theorem insertByRank_distinct (x : Nat × List Char) : ∀ l : List (Nat × List Char),
    l.Pairwise (fun a b => a.1 ≠ b.1) → (∀ y ∈ l, x.1 ≠ y.1) →
    (insertByRank x l).Pairwise (fun a b => a.1 ≠ b.1) := by
  intro l
  induction l with
  | nil => intro _ _; simp [insertByRank]
  | cons z zs ih =>
      intro h hx
      rw [List.pairwise_cons] at h
      rw [insertByRank]
      by_cases hle : x.1 ≤ z.1
      · rw [if_pos hle]
        exact List.pairwise_cons.2 ⟨hx, List.pairwise_cons.2 h⟩
      · rw [if_neg hle]
        refine List.pairwise_cons.2 ⟨?_, ih h.2 (fun y hy => hx y (by simp [hy]))⟩
        intro b hb
        rcases (insertByRank_mem x b zs).1 hb with hb' | hb'
        · rw [hb']; exact fun hc => hx z (by simp) hc.symm
        · exact h.1 b hb'

theorem sortByRank_distinct : ∀ l : List (Nat × List Char),
    l.Pairwise (fun a b => a.1 ≠ b.1) → (sortByRank l).Pairwise (fun a b => a.1 ≠ b.1) := by
  intro l
  induction l with
  | nil => intro _; simp [sortByRank_nil]
  | cons x xs ih =>
      intro h
      rw [List.pairwise_cons] at h
      rw [sortByRank_cons]
      exact insertByRank_distinct x _ (ih h.2) (fun y hy => h.1 y ((sortByRank_mem y xs).1 hy))

/-- **The sort is the identity on a list that is already in rank order.**  This
is the prose half of the document round trip: `splitDoc` reads prose in line
order, so `renderDocAt` puts it back exactly where it was. -/
theorem sortByRank_id : ∀ l : List (Nat × List Char),
    l.Pairwise (fun a b => a.1 ≤ b.1) → sortByRank l = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro h
      rw [List.pairwise_cons] at h
      rw [sortByRank_cons, ih h.2]
      cases xs with
      | nil => rfl
      | cons z zs =>
          rw [insertByRank, if_pos (h.1 z (by simp))]

/-- **And the sorted list is the file's line list**: strictly ordered by rank,
so `sorted_ext_by_key` pins it down from its members alone. -/
theorem sortByRank_strict (l : List (Nat × List Char))
    (h : (l.map Prod.fst).Nodup) :
    (sortByRank l).Pairwise (fun a b => a.1 < b.1) :=
  pairwise_lt_of_le_ne (fun a : Nat × List Char => a.1) (sortByRank_sorted l)
    (sortByRank_distinct l (pairwise_ne_of_nodup_keys (fun a : Nat × List Char => a.1) h))


/-! ## JSON -/

def jsonErr (s : String) : Json := Json.mkObj [("err", Json.str s)]

def getStr (j : Json) (k : String) : Except String String := j.getObjValAs? String k
def getNat (j : Json) (k : String) : Except String Nat := j.getObjValAs? Nat k

def getArr (j : Json) (k : String) : Except String (Array Json) := do
  let v ← j.getObjVal? k
  v.getArr?

def strLines (j : Json) : Except String (List (List Char)) := do
  let a ← j.getArr?
  let mut out : List (List Char) := []
  for x in a do
    let s ← x.getStr?
    out := out ++ [s.toList]
  return out

structure ReqDoc where
  path  : String
  reg   : Option Region
  lines : List (List Char)

def parseRegion (j : Json) : Except String (Option Region) := do
  match j.getObjVal? "grain" with
  | .error _ => return none
  | .ok gv =>
    match gv with
    | .null => return none
    | _ =>
      let gn ← gv.getNat?
      match Grain.ofNat? gn with
      | none   => throw s!"grain {gn} out of range (0..{grainCount - 1})"
      | some g =>
        let ix ← getNat j "ix"
        return some ⟨g, ix⟩

def parseDoc (j : Json) : Except String ReqDoc := do
  let path ← getStr j "path"
  let reg ← parseRegion j
  let lv ← j.getObjVal? "lines"
  let lines ← strLines lv
  return ⟨path, reg, lines⟩

/-- One command as the UI sends it. -/
inductive ReqCmd
  | move (i : Id) (doc : DocIx)
  | drop (i : Id)
  | est  (i : Id) (v : Nat)
  | demote (i : Id) (doc : DocIx) (period : Nat)
  | readopt (i : Id) (doc : DocIx)

def parseCmd (j : Json) : Except String ReqCmd := do
  let op ← getStr j "op"
  match op with
  | "move" => return .move (← getStr j "id").toList (← getNat j "doc")
  | "drop" => return .drop (← getStr j "id").toList
  | "est"  => return .est (← getStr j "id").toList (← getNat j "min")
  | "demote" => return .demote (← getStr j "id").toList (← getNat j "doc") (← getNat j "period")
  | "readopt" => return .readopt (← getStr j "id").toList (← getNat j "doc")
  | _ => throw s!"unknown op {op}"

def kerrName : KErr → String
  | .occupied   => "occupied"
  | .noSuchId   => "noSuchId"
  | .notDemoted => "notDemoted"
  | .badHorizon => "badHorizon"

/-- Fresh rank in the destination document: strictly greater than every rank
already there, so a move can never collide on a rank either.  `freshRank_gt`
below is that claim, which the first version asserted in a comment. -/
def docProseMax (p : PlanCore) (k : DocIx) : Nat :=
  match p.docs[k]? with
  | none   => 0
  | some d => d.prose.foldl (fun a q => Nat.max a q.1) 0

def docLineMax (p : PlanCore) (k : DocIx) : Nat :=
  (p.lines.filter (fun l => l.site.doc == k)).foldl (fun acc l => Nat.max acc l.site.rank) 0

def freshRank (p : PlanCore) (k : DocIx) : Nat :=
  Nat.max (docProseMax p k) (docLineMax p k) + 1

theorem foldl_max_ge (f : Line → Nat) : ∀ (xs : List Line) (a : Nat),
    a ≤ xs.foldl (fun acc y => Nat.max acc (f y)) a := by
  intro xs
  induction xs with
  | nil => intro a; exact Nat.le_refl a
  | cons x t ih => intro a; exact Nat.le_trans (Nat.le_max_left a (f x)) (ih _)

theorem le_foldl_max (f : Line → Nat) (l : Line) : ∀ (xs : List Line) (a : Nat),
    l ∈ xs → f l ≤ xs.foldl (fun acc y => Nat.max acc (f y)) a := by
  intro xs
  induction xs with
  | nil => intro a h; simp at h
  | cons x t ih =>
      intro a h
      simp only [List.foldl_cons]
      rcases List.mem_cons.1 h with rfl | h'
      · exact Nat.le_trans (Nat.le_max_right a (f l)) (foldl_max_ge f t _)
      · exact ih _ h'

/-- **The rank a move lands on is fresh.**  Every line already in the
destination has a strictly smaller rank, so a relocation cannot collide on a
rank — and, read the other way, moving an item back into the file it came from
does *not* restore its rank, which is L4b. -/
theorem freshRank_gt (p : PlanCore) (k : DocIx) (l : Line) (h : l ∈ p.lines)
    (hk : l.site.doc = k) : l.site.rank < freshRank p k := by
  have hmem : l ∈ p.lines.filter (fun x => x.site.doc == k) := by
    simp [List.mem_filter, h, hk]
  have hle : l.site.rank ≤ docLineMax p k := le_foldl_max (fun x => x.site.rank) l _ 0 hmem
  have hmx := Nat.le_max_right (docProseMax p k) (docLineMax p k)
  exact Nat.lt_succ_of_le (Nat.le_trans hle hmx)

theorem live_line_mem (p : PlanCore) (i : Id) (e : Entity) (h : p.store.get i = some e) :
    (⟨i, e.val.live, serializeItem i (glyphAt e.val e.val.live) e.val.line⟩ : Line) ∈ p.lines := by
  unfold PlanCore.lines
  simp only [List.mem_flatMap]
  refine ⟨i, (p.store.domSpec i).mpr (by rw [h]; rfl), ?_⟩
  rw [h]
  unfold render renderCore
  simp

/-- **L4b at the boundary.**  `move ^id <file>` back to the file the item came
from does not undo the first move: the wire command carries a document, and the
rank it lands on is generated fresh.  So `tm undo` replays the log; it does not
apply an inverse command. -/
theorem move_out_and_back_is_not_the_inverse (p : WfPlan) (i : Id) (e a : Entity) (t : Site)
    (hget : p.val.store.get i = some e) (h : moveTo t e = .ok a) :
    (moveTo ⟨e.val.live.doc, freshRank p.val e.val.live.doc⟩ a).map Subtype.val ≠ .ok e.val := by
  refine move_back_at_a_fresh_rank_is_not_the_inverse t _ e a ?_ h
  have h2 : e.val.live.rank < freshRank p.val e.val.live.doc :=
    freshRank_gt p.val e.val.live.doc _ (live_line_mem p.val i e hget) rfl
  omega

/-- Every relocating command resolves its destination against `docs` first, so
the `Nat` off the wire never reaches a `Site`.  An index past the end of `docs`
is `badHorizon` — before this, it deleted the item and returned `ok`.  A
destination that exists but is not ahead of the item's tombstone is `badHorizon`
too, from `mapAt`'s re-check rather than from `resolveDest`: it is a fact about
the item, not about the index. -/
def applyCmd (c : ReqCmd) (p : WfPlan) : Except KErr WfPlan :=
  match c with
  | .move i d       =>
    match resolveDest p.val d with
    | .error k => .error k
    | .ok dd   => cmdMove i (freshRank p.val dd.ix) p dd
  | .drop i         => cmdDrop i p
  | .est i v        => cmdSetEst v i p
  | .demote i d per =>
    match resolveDest p.val d with
    | .error k => .error k
    | .ok dd   => cmdDemote i (freshRank p.val dd.ix) per p dd
  | .readopt i d    =>
    match resolveDest p.val d with
    | .error k => .error k
    | .ok dd   => cmdReadopt i (freshRank p.val dd.ix) p dd

/-- **Error 2, as a theorem.**  A destination that is not a document is
rejected, and the plan is untouched. -/
theorem move_to_a_document_that_does_not_exist_is_rejected (p : WfPlan) (i : Id) (n : Nat)
    (h : ¬ n < p.val.docs.length) : applyCmd (.move i n) p = .error .badHorizon := by
  simp [applyCmd, resolveDest, h]

theorem demote_to_a_document_that_does_not_exist_is_rejected (p : WfPlan) (i : Id) (n per : Nat)
    (h : ¬ n < p.val.docs.length) : applyCmd (.demote i n per) p = .error .badHorizon := by
  simp [applyCmd, resolveDest, h]

def applyAll : List ReqCmd → WfPlan → Except KErr WfPlan
  | [],      p => .ok p
  | c :: cs, p => (applyCmd c p).bind (applyAll cs)

/-- Closure over a whole request: whatever the host receives passes the same
decidable checker that admitted the input. -/
theorem applyAll_closed (cs : List ReqCmd) (p : WfPlan) (q : PlanCore)
    (h : (applyAll cs p).map Subtype.val = .ok q) : planWf q = true := by
  cases hr : applyAll cs p with
  | error k => rw [hr] at h; simp [Except.map] at h
  | ok r =>
      rw [hr] at h
      simp only [Except.map, Except.ok.injEq] at h
      subst h
      exact r.property

def lerrJson : LErr → Json
  | .dupId i          => Json.mkObj [("dupId", Json.str (String.ofList i))]
  | .orphanDemotion i => Json.mkObj [("orphanDemotion", Json.str (String.ofList i))]
  | .splitLine i      => Json.mkObj [("splitLine", Json.str (String.ofList i))]
  | .notADemotion i   => Json.mkObj [("notADemotion", Json.str (String.ofList i))]
  | .ambiguousDemotion i => Json.mkObj [("ambiguousDemotion", Json.str (String.ofList i))]
  | .duplicatePath pa => Json.mkObj [("duplicatePath", Json.str (String.ofList pa))]
  | .badLine pa n w   => Json.mkObj [("badLine", Json.mkObj
      [("path", Json.str (String.ofList pa)), ("line", Json.num n), ("why", Json.str (toString (repr w)))])]

/-- Name the id whose two lines the documents do not order, for the diagnostic.
Every diagnostic names the id or the path it is about. -/
def firstUnoriented (p : PlanCore) : Option Id :=
  p.store.dom.find? (fun i =>
    match p.store.get i with
    | none   => false
    | some e => !demotionOriented p e)

/-- Name the path two documents share, for the diagnostic. -/
def firstDupPath : List (List Char) → Option (List Char)
  | []      => none
  | x :: xs => if x ∈ xs then some x else firstDupPath xs

theorem firstDupPath_none (l : List (List Char)) (h : firstDupPath l = none) : l.Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
      unfold firstDupPath at h
      split at h
      · simp at h
      · rename_i hc
        exact List.nodup_cons.2 ⟨hc, ih h⟩

/-- A document's horizon, in the shape `parseRegion` reads back.  The response
carries it because the request does: a demotion's two lines are told apart by
the regions of their files, so a response that dropped them would be a response
the kernel could not read (`the_kernel_reads_back_what_it_writes`). -/
def regionJson (r : Option Region) : List (String × Json) :=
  match r with
  | none   => []
  | some g => [("grain", Json.num g.grain.val), ("ix", Json.num g.ix)]

/-! ## The plan-level round trip

`renderSplit_splitDoc` (Plan.lean) is the round trip for one file's *text*, and
`load_render_line` / `paired_renders_each_placement` are the round trip through
the *entity* the loader builds.  Between them there was a gap, and it is the gap
that hid the `[-]` regression: the pipeline takes a document's item lines apart,
files them under their ids in a store, and reads them back out **in the order
the store enumerates its domain**, which has nothing to do with the file.  That
the bytes survive that detour was checked by a test that fed the kernel its own
output back — not proved.

This section proves it.  The chain is:

* `placementsOf` — every item line of the request, with the index and horizon of
  the file it came from, as a recursion the proofs can induct on;
* `buildEntities_spec`, `loadStore_get_of_mem` / `loadStore_get_some` — the
  store holds exactly one entity per id and nothing else;
* `buildEntity_renders` — **the entity an id's lines build renders exactly those
  lines back**, which is `load_render_line` and `paired_renders_each_placement`
  turned from "the bytes agree" into "the *set* of lines agrees";
* `loadCore_lines_mem` — so the plan's whole line list is exactly the request's
  placements, and the store's enumeration order has dropped out;
* `sorted_ext_by_key` plus `Normalized` — so putting them back in rank order
  reproduces the file, and `the_kernel_reads_back_what_it_writes` below says so
  for every document of every request the loader accepts.
-/

/-- The `Doc` a request document becomes: its path, its **prose only**, and the
horizon it declares. -/
def mkDoc (d : ReqDoc) : Doc := ⟨d.path.toList, (splitDoc 0 d.lines).prose, d.reg⟩

/-- Every item line of a whole request, each carrying the index and the horizon
of the document it was read from.  A recursion over the documents rather than
`zipIdx` over them, so that `mem_placementsOf` is an induction. -/
def placementsOf : Nat → List ReqDoc → List Placement
  | _, []        => []
  | k, d :: rest => placementsOfDoc k d.reg (splitDoc 0 d.lines) ++ placementsOf (k + 1) rest

theorem mem_placementsOfDoc {k : DocIx} {reg : Option Region} {s : DocSplit} {q : Placement} :
    q ∈ placementsOfDoc k reg s ↔
      ∃ it ∈ s.items, q = ⟨k, it.1, it.2.1, it.2.2.1, it.2.2.2, reg⟩ := by
  unfold placementsOfDoc
  constructor
  · intro h
    obtain ⟨it, hit, hq⟩ := List.mem_map.1 h
    exact ⟨it, hit, hq.symm⟩
  · rintro ⟨it, hit, rfl⟩
    exact List.mem_map.2 ⟨it, hit, rfl⟩

theorem mem_placementsOf (q : Placement) : ∀ (k : Nat) (ds : List ReqDoc),
    q ∈ placementsOf k ds ↔
      ∃ j, ∃ d : ReqDoc, ds[j]? = some d ∧
        q ∈ placementsOfDoc (k + j) d.reg (splitDoc 0 d.lines) := by
  intro k ds
  induction ds generalizing k with
  | nil => simp [placementsOf]
  | cons d rest ih =>
      rw [placementsOf, List.mem_append, ih (k + 1)]
      constructor
      · rintro (h | ⟨j, d', hd', hq⟩)
        · exact ⟨0, d, by simp, by simpa using h⟩
        · refine ⟨j + 1, d', by simpa using hd', ?_⟩
          rw [show k + (j + 1) = (k + 1) + j from by omega]
          exact hq
      · rintro ⟨j, d', hd', hq⟩
        cases j with
        | zero =>
            left
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hd'
            rw [hd']
            simpa using hq
        | succ m =>
            right
            refine ⟨m, d', by simpa using hd', ?_⟩
            rw [show (k + 1) + m = k + (m + 1) from by omega]
            exact hq

/-! ### The store the loader builds -/

theorem buildEntities_fold : ∀ (ps : List Placement) (is : List Id)
    (acc out : List (Id × Entity)),
    is.foldlM (fun acc i => do
        let e ← buildEntity i (ps.filter (fun q => q.id == i))
        pure (acc ++ [(i, e)])) acc = Except.ok out →
    ∃ tl : List (Id × Entity), out = acc ++ tl ∧ tl.map Prod.fst = is ∧
      ∀ ie ∈ tl, buildEntity ie.1 (ps.filter (fun q => q.id == ie.1)) = .ok ie.2 := by
  intro ps is
  induction is with
  | nil =>
      intro acc out h
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨[], by rw [← h, List.append_nil], rfl, by simp⟩
  | cons i rest ih =>
      intro acc out h
      rw [List.foldlM_cons] at h
      cases hbe : buildEntity i (ps.filter (fun q => q.id == i)) with
      | error k =>
          rw [hbe] at h
          exact absurd (show (Except.error k : Except LErr (List (Id × Entity)))
            = Except.ok out from h) (by simp)
      | ok e =>
          rw [hbe] at h
          simp only [Except.bind, pure, Except.pure] at h
          obtain ⟨tl, hout, hmap, hall⟩ := ih (acc ++ [(i, e)]) out h
          refine ⟨(i, e) :: tl, ?_, by simp [hmap], ?_⟩
          · rw [hout, List.append_assoc, List.singleton_append]
          · intro ie hie
            rcases List.mem_cons.1 hie with hh | hh
            · rw [hh]; exact hbe
            · exact hall ie hh

theorem buildEntities_spec (ps : List Placement) (items : List (Id × Entity))
    (h : buildEntities ps = .ok items) :
    items.map Prod.fst = dedupIds (ps.map Placement.id) ∧
      ∀ ie ∈ items, buildEntity ie.1 (ps.filter (fun q => q.id == ie.1)) = .ok ie.2 := by
  obtain ⟨tl, hout, hmap, hall⟩ := buildEntities_fold ps (dedupIds (ps.map Placement.id)) [] items h
  rw [List.nil_append] at hout
  subst hout
  exact ⟨hmap, hall⟩

theorem Store.insert_get (s : Store) (i j : Id) (e : Entity) :
    (s.insert i e).get j = if j = i then some e else s.get j := by
  unfold Store.insert
  split <;> rfl

theorem loadStore_fold_not_mem : ∀ (items : List (Id × Entity)) (s : Store) (i : Id),
    i ∉ items.map Prod.fst →
    (items.foldl (fun s p => s.insert p.1 p.2) s).get i = s.get i := by
  intro items
  induction items with
  | nil => intro s i _; rfl
  | cons a t ih =>
      intro s i h
      simp only [List.map_cons, List.mem_cons, not_or] at h
      rw [List.foldl_cons, ih _ i h.2, Store.insert_get, if_neg h.1]

theorem loadStore_fold_mem : ∀ (items : List (Id × Entity)) (s : Store) (i : Id) (e : Entity),
    (i, e) ∈ items → (items.map Prod.fst).Nodup →
    (items.foldl (fun s p => s.insert p.1 p.2) s).get i = some e := by
  intro items
  induction items with
  | nil => intro s i e h _; simp at h
  | cons a t ih =>
      intro s i e h hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 h with hh | hh
      · have hi : a.1 = i := by rw [← hh]
        have he : a.2 = e := by rw [← hh]
        rw [List.foldl_cons, loadStore_fold_not_mem t _ i (by rw [hi] at hnd; exact hnd.1),
          Store.insert_get, if_pos hi.symm, he]
      · rw [List.foldl_cons]
        exact ih _ i e hh hnd.2

theorem loadStore_fold_some : ∀ (items : List (Id × Entity)) (s : Store) (i : Id) (e : Entity),
    (items.foldl (fun s p => s.insert p.1 p.2) s).get i = some e →
    (i, e) ∈ items ∨ s.get i = some e := by
  intro items
  induction items with
  | nil => intro s i e h; exact Or.inr h
  | cons a t ih =>
      intro s i e h
      rw [List.foldl_cons] at h
      rcases ih _ i e h with hh | hh
      · exact Or.inl (List.mem_cons.2 (Or.inr hh))
      · rw [Store.insert_get] at hh
        by_cases hia : i = a.1
        · rw [if_pos hia] at hh
          injection hh with hh
          exact Or.inl (List.mem_cons.2 (Or.inl (by rw [hia, ← hh])))
        · rw [if_neg hia] at hh
          exact Or.inr hh

theorem loadStore_get_of_mem (items : List (Id × Entity)) (i : Id) (e : Entity)
    (hnd : (items.map Prod.fst).Nodup) (hm : (i, e) ∈ items) :
    (loadStore items).get i = some e :=
  loadStore_fold_mem items emptyStore i e hm hnd

theorem loadStore_get_some (items : List (Id × Entity)) (i : Id) (e : Entity)
    (h : (loadStore items).get i = some e) : (i, e) ∈ items := by
  rcases loadStore_fold_some items emptyStore i e h with hh | hh
  · exact hh
  · simp [emptyStore] at hh

theorem mem_lines_of_render (p : PlanCore) (i : Id) (e : Entity) (l : Line)
    (hget : p.store.get i = some e) (hl : l ∈ render i e) : l ∈ p.lines := by
  unfold PlanCore.lines
  refine List.mem_flatMap.2 ⟨i, (p.store.domSpec i).mpr (by rw [hget]; rfl), ?_⟩
  rw [hget]
  exact hl

/-! ### The entity an id's lines build renders exactly those lines

`load_render_line` and `paired_renders_each_placement` say the *bytes* of each
line survive.  This says the *list* does: nothing extra is emitted and nothing
is dropped.  It is the step that turns a fact about one line into a fact about a
document. -/

/-- The line a placement was read from: its site, and the bytes `serializeItem`
writes back for the id, box and token vector the parser returned. -/
def placementLine (q : Placement) : Line :=
  ⟨q.id, ⟨q.doc, q.rank⟩, serializeItem q.id q.glyph q.item⟩

theorem loneEntity_archive (i : Id) (q : Placement) (e : Entity)
    (h : loneEntity i q = .ok e) : e.val.archive = none := by
  unfold loneEntity at h
  split at h
  · injection h with h; rw [← h]
  · simp at h

theorem buildEntity_renders (i : Id) (qs : List Placement) (e : Entity)
    (hid : ∀ q ∈ qs, q.id = i) (h : buildEntity i qs = .ok e) (l : Line) :
    l ∈ render i e ↔ ∃ q ∈ qs, l = placementLine q := by
  match qs with
  | [] => simp [buildEntity] at h
  | [q] =>
      have h' : loneEntity i q = .ok e := h
      have hq : q.id = i := hid q (by simp)
      obtain ⟨hlive, hline, hglyph⟩ := lone_placement_renders_back i q e h'
      have harch := loneEntity_archive i q e h'
      have hr : render i e = [placementLine q] := by
        unfold render renderCore placementLine
        simp only [harch]
        rw [hglyph, hline, hlive, hq]
      rw [hr]
      simp
  | [a, b] =>
      have h' : pairedEntity i a b = .ok e := h
      have ha : a.id = i := hid a (by simp)
      have hb : b.id = i := hid b (by simp)
      obtain ⟨arch, live, hor, _, hlive, harch, hline, hitem, hag, hg, hd⟩ :=
        paired_placement_renders_back i a b e h'
      have hcases := (orientPair_cases hor).1
      have hAitem : arch.item = live.item := by
        rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2]; exact hitem
        · rw [e1, e2]; exact hitem.symm
      have hAid : arch.id = i := by
        rcases hcases with ⟨e1, _⟩ | ⟨e1, _⟩
        · rw [e1]; exact ha
        · rw [e1]; exact hb
      have hLid : live.id = i := by
        rcases hcases with ⟨_, e2⟩ | ⟨_, e2⟩
        · rw [e2]; exact hb
        · rw [e2]; exact ha
      have hAB : ∀ x : Placement, (x = live ∨ x = arch) ↔ (x = a ∨ x = b) := by
        intro x
        rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2]; exact Or.comm
        · rw [e1, e2]
      have hr : render i e = [placementLine live, placementLine arch] := by
        unfold render renderCore placementLine
        simp only [harch]
        rw [hd, hg, hline, hlive, hLid, hAid, hag, hAitem]
      rw [hr]
      constructor
      · intro hl
        rcases List.mem_cons.1 hl with h1 | h1
        · exact ⟨live, by simpa using (hAB live).1 (Or.inl rfl), h1⟩
        · rcases List.mem_cons.1 h1 with h2 | h2
          · exact ⟨arch, by simpa using (hAB arch).1 (Or.inr rfl), h2⟩
          · simp at h2
      · rintro ⟨q, hq, hlq⟩
        rcases (hAB q).2 (by simpa using hq) with h1 | h1
        · exact List.mem_cons.2 (Or.inl (by rw [hlq, h1]))
        · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl (by rw [hlq, h1]))))
  | _ :: _ :: _ :: _ => simp [buildEntity] at h

/-! ### The plan the loader builds, and its line list -/

def loadCore (docs : List ReqDoc) (items : List (Id × Entity)) : PlanCore :=
  ⟨docs.map mkDoc, loadStore items⟩

/-- The document half of `planWf` is established **by construction**: prose is
exactly what did not parse as an item, so there is no separate validator to
drift. -/
theorem loadCore_docsWf (docs : List ReqDoc) (items : List (Id × Entity)) :
    docsWf (loadCore docs items) = true := by
  show List.all (docs.map mkDoc) docWf = true
  simp only [List.all_eq_true, List.mem_map]
  rintro d ⟨x, _, rfl⟩
  show List.all (splitDoc 0 x.lines).prose (fun q => !isItemLine q.2) = true
  simp only [List.all_eq_true]
  intro q hq
  simp [splitDoc_prose_not_item 0 x.lines q hq]

/-- **The plan's line list is exactly the request's item lines.**  The store's
enumeration order has dropped out entirely: nothing the loader built renders a
line the files did not contain, and no line of a file is missing. -/
theorem loadCore_lines_mem (docs : List ReqDoc) (items : List (Id × Entity))
    (hb : buildEntities (placementsOf 0 docs) = .ok items) (l : Line) :
    l ∈ (loadCore docs items).lines ↔ ∃ q ∈ placementsOf 0 docs, l = placementLine q := by
  obtain ⟨hmap, hall⟩ := buildEntities_spec _ _ hb
  have hnd : (items.map Prod.fst).Nodup := by rw [hmap]; exact dedupIds_nodup _
  constructor
  · intro h
    obtain ⟨i, e, hget, _, hl⟩ := lines_mem (loadCore docs items) l h
    have hmem : (i, e) ∈ items := loadStore_get_some items i e hget
    have hbe := hall (i, e) hmem
    have hidf : ∀ q ∈ (placementsOf 0 docs).filter (fun q => q.id == i), q.id = i := by
      intro q hq
      simpa using (List.mem_filter.1 hq).2
    obtain ⟨q, hq, hlq⟩ := (buildEntity_renders i _ e hidf hbe l).1 hl
    exact ⟨q, (List.mem_filter.1 hq).1, hlq⟩
  · rintro ⟨q, hq, hlq⟩
    have hidin : q.id ∈ items.map Prod.fst := by
      rw [hmap, mem_dedupIds]
      exact List.mem_map.2 ⟨q, hq, rfl⟩
    obtain ⟨ie, hie, hid⟩ := List.mem_map.1 hidin
    have hget : (loadCore docs items).store.get ie.1 = some ie.2 :=
      loadStore_get_of_mem items ie.1 ie.2 hnd hie
    have hbe := hall ie hie
    have hidf : ∀ x ∈ (placementsOf 0 docs).filter (fun x => x.id == ie.1), x.id = ie.1 := by
      intro x hx
      simpa using (List.mem_filter.1 hx).2
    have hqf : q ∈ (placementsOf 0 docs).filter (fun x => x.id == ie.1) :=
      List.mem_filter.2 ⟨hq, by simp [hid]⟩
    have := (buildEntity_renders ie.1 _ ie.2 hidf hbe l).2 ⟨q, hqf, hlq⟩
    exact mem_lines_of_render _ ie.1 ie.2 l hget this

/-- The placements of one document are exactly its own item lines. -/
theorem placements_of_doc (docs : List ReqDoc) (k : Nat) (rd : ReqDoc)
    (hk : docs[k]? = some rd) (q : Placement) :
    (q ∈ placementsOf 0 docs ∧ q.doc = k) ↔
      ∃ it ∈ (splitDoc 0 rd.lines).items,
        q = ⟨k, it.1, it.2.1, it.2.2.1, it.2.2.2, rd.reg⟩ := by
  constructor
  · rintro ⟨hq, hdoc⟩
    obtain ⟨j, d, hd', hqj⟩ := (mem_placementsOf q 0 docs).1 hq
    obtain ⟨it, hit, hqe⟩ := mem_placementsOfDoc.1 hqj
    have hjk : j = k := by rw [hqe] at hdoc; simpa using hdoc
    subst hjk
    rw [hd'] at hk
    injection hk with hk
    subst hk
    exact ⟨it, hit, by rw [hqe]; simp⟩
  · rintro ⟨it, hit, rfl⟩
    refine ⟨(mem_placementsOf _ 0 docs).2 ⟨k, rd, hk, ?_⟩, rfl⟩
    exact mem_placementsOfDoc.2 ⟨it, hit, by simp⟩

/-- The `(rank, bytes)` pair one parsed item line becomes. -/
def itemLine (it : Nat × (Id × Glyph × RawItem)) : Nat × List Char :=
  (it.1, serializeItem it.2.1 it.2.2.1 it.2.2.2)

/-- **The plan-level round trip.**  Every document of a plan the loader built
renders back, byte for byte, to the lines it was read from — prose interleaved
with item lines whose state box and `^id` were regenerated from the entity, and
whose *order* was reconstructed from ranks rather than remembered.

`normalized` is where rank distinctness does its work: without it the sorted
list would not be determined by its members, and which of two lines sharing a
rank came first would depend on the order the store enumerated its domain. -/
theorem renderDocAt_loadCore (docs : List ReqDoc) (items : List (Id × Entity))
    (hb : buildEntities (placementsOf 0 docs) = .ok items)
    (hnorm : normalized (loadCore docs items) = true)
    (k : Nat) (rd : ReqDoc) (hk : docs[k]? = some rd) :
    renderDocAt (loadCore docs items) k (mkDoc rd) = rd.lines := by
  have hklt : k < (loadCore docs items).docs.length := by
    have hlen : k < docs.length := by
      obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hk
      exact h1
    show k < (docs.map mkDoc).length
    simpa using hlen
  -- rank distinctness for the document's item lines, out of `normalized`
  have hkeys : (((((loadCore docs items).lines.filter (fun l => l.site.doc == k)).map
      (fun l => (l.site.rank, l.text))).map Prod.fst)).Nodup := by
    simp only [List.map_map]
    have hnd : (docRanks (loadCore docs items) k).Nodup := by
      simp only [normalized, List.all_eq_true, decide_eq_true_eq] at hnorm
      exact hnorm k (List.mem_range.2 hklt)
    rw [docRanks_eq] at hnd
    exact (List.nodup_append.1 hnd).2.1
  have hX : sortByRank (((loadCore docs items).lines.filter (fun l => l.site.doc == k)).map
      (fun l => (l.site.rank, l.text)))
      = (splitDoc 0 rd.lines).items.map itemLine := by
    refine sorted_ext_by_key (fun x : Nat × List Char => x.1) _ _
      (sortByRank_strict _ hkeys) ?_ ?_
    · rw [List.pairwise_map]
      exact splitDoc_items_sorted 0 rd.lines
    · intro x
      rw [sortByRank_mem]
      constructor
      · intro hx
        obtain ⟨l, hl, hxl⟩ := List.mem_map.1 hx
        have hlf := List.mem_filter.1 hl
        obtain ⟨q, hq, rfl⟩ := (loadCore_lines_mem docs items hb l).1 hlf.1
        have hqd : q.doc = k := by simpa [placementLine] using hlf.2
        obtain ⟨it, hit, rfl⟩ := (placements_of_doc docs k rd hk q).1 ⟨hq, hqd⟩
        exact List.mem_map.2 ⟨it, hit, by rw [← hxl]; rfl⟩
      · intro hx
        obtain ⟨it, hit, hxit⟩ := List.mem_map.1 hx
        refine List.mem_map.2 ⟨placementLine ⟨k, it.1, it.2.1, it.2.2.1, it.2.2.2, rd.reg⟩, ?_, ?_⟩
        · refine List.mem_filter.2 ⟨?_, by simp [placementLine]⟩
          exact (loadCore_lines_mem docs items hb _).2
            ⟨_, ((placements_of_doc docs k rd hk _).2 ⟨it, hit, rfl⟩).1, rfl⟩
        · rw [← hxit]; rfl
  show weave (sortByRank (mkDoc rd).prose) _ = rd.lines
  rw [hX]
  show weave (sortByRank (splitDoc 0 rd.lines).prose) _ = rd.lines
  rw [sortByRank_id _ (splitDoc_prose_sorted 0 rd.lines)]
  exact renderSplit_splitDoc 0 rd.lines

/-! ### The loader as one function, and the round trip through it -/

/-- Build the plan from a parsed request: one entity per id, one `Doc` per
request document, and then the four decidable plan-level checks, each returning
the diagnostic it is named by. -/
def loadPlan (docs : List ReqDoc) : Except Json WfPlan :=
  match buildEntities (placementsOf 0 docs) with
  | .error e => .error (Json.mkObj [("err", lerrJson e)])
  | .ok items =>
    if hpath : pathsDistinct (loadCore docs items) = true then
      if hsites : sitesInRange (loadCore docs items) = true then
        if hor : demotionsOriented (loadCore docs items) = true then
          if hitems : itemsWf (loadCore docs items) = true then
            .ok ⟨loadCore docs items,
              planWf_of_parts (loadCore_docsWf docs items) hsites hpath hor hitems⟩
          else
            .error (Json.mkObj [("err", Json.mkObj
              [("itemCheck", Json.str (firstItemFault (loadCore docs items)))])])
        else
          .error (Json.mkObj [("err", lerrJson (.ambiguousDemotion
            ((firstUnoriented (loadCore docs items)).getD [])))])
      else
        .error (Json.mkObj [("err", Json.mkObj [("kernel", Json.str "siteOutOfRange")])])
    else
      .error (Json.mkObj [("err", lerrJson (.duplicatePath
        ((firstDupPath (docs.map (fun d => d.path.toList))).getD [])))])

theorem loadPlan_spec (docs : List ReqDoc) (p : WfPlan) (h : loadPlan docs = .ok p) :
    ∃ items, buildEntities (placementsOf 0 docs) = .ok items ∧ p.val = loadCore docs items := by
  unfold loadPlan at h
  split at h
  · simp at h
  · rename_i items hbe
    split at h
    · split at h
      · split at h
        · split at h
          · refine ⟨items, hbe, ?_⟩
            injection h with h
            rw [← h]
          · simp at h
        · simp at h
      · simp at h
    · simp at h

/-- **The gap that hid the `[-]` bug, closed.**  For every document of every
request the loader accepts, taking the file apart into prose and entities and
reading it back out through `renderDocAt` reproduces the input lines exactly.

Until now this was checked by a test (`the_kernel_reads_back_what_it_writes` in
the Rust suite) that demoted an item and fed the kernel's own output back in.  A
test covers the shapes someone thought of; the `[-]` regression is exactly the
shape nobody did. -/
theorem the_kernel_reads_back_what_it_writes (docs : List ReqDoc) (p : WfPlan)
    (h : loadPlan docs = .ok p) (k : Nat) (rd : ReqDoc) (hk : docs[k]? = some rd) :
    p.val.docs[k]? = some (mkDoc rd) ∧ renderDocAt p.val k (mkDoc rd) = rd.lines := by
  obtain ⟨items, hb, hval⟩ := loadPlan_spec docs p h
  have hnorm : normalized (loadCore docs items) = true :=
    (itemsWf_parts (planWf_parts (hval ▸ p.property)).2.2.2.2).1
  refine ⟨?_, ?_⟩
  · rw [hval]
    show (docs.map mkDoc)[k]? = some (mkDoc rd)
    rw [List.getElem?_map, hk]
    rfl
  · rw [hval]
    exact renderDocAt_loadCore docs items hb hnorm k rd hk

/-- **The same, at the exact call site.**  `runPlan` renders `p.val.docs.zipIdx`,
so this is the statement for every `(document, index)` pair it actually hands to
`renderDocAt`: the bytes it emits for that document are the bytes the request
sent for it.  What is left unverified between here and the wire is the JSON
string wrapper — splitting a file on newlines and joining it again, which is
README gap 6 and is not this theorem's business. -/
theorem runPlan_renders_the_input (docs : List ReqDoc) (p : WfPlan)
    (h : loadPlan docs = .ok p) (d : Doc) (j : Nat) (hj : (d, j) ∈ p.val.docs.zipIdx) :
    ∃ rd : ReqDoc, docs[j]? = some rd ∧ d = mkDoc rd ∧ renderDocAt p.val j d = rd.lines := by
  obtain ⟨items, hb, hval⟩ := loadPlan_spec docs p h
  have hget : p.val.docs[j]? = some d := List.mem_zipIdx_iff_getElem?.1 hj
  rw [hval] at hget
  have hget' : (docs.map mkDoc)[j]? = some d := hget
  rw [List.getElem?_map] at hget'
  cases hd : docs[j]? with
  | none => rw [hd] at hget'; simp at hget'
  | some rd =>
      rw [hd] at hget'
      simp only [Option.map_some, Option.some.injEq] at hget'
      obtain ⟨_, hr⟩ := the_kernel_reads_back_what_it_writes docs p h j rd hd
      exact ⟨rd, rfl, hget'.symm, by rw [← hget']; exact hr⟩

/-- Apply the request's commands and render every document back to text. -/
def runPlan (plan : WfPlan) (cmds : List ReqCmd) : Except Json Json := do
  let plan' ←
    match applyAll cmds plan with
    | .ok q => pure q
    | .error k => throw (Json.mkObj [("err", Json.mkObj [("kernel", Json.str (kerrName k))])])
  let outDocs := (plan'.val.docs.zipIdx.map (fun p =>
    Json.mkObj
      ([("path", Json.str (String.ofList p.1.path)),
        ("lines", Json.arr ((renderDocAt plan'.val p.2 p.1).map
          (fun l => Json.str (String.ofList l))).toArray)] ++ regionJson p.1.region)))
  return Json.mkObj [("ok", Json.mkObj [("docs", Json.arr outDocs.toArray)])]

def run (j : Json) : Except Json Json := do
  let docsJ ←
    match getArr j "docs" with
    | .ok a => pure a
    | .error e => throw (jsonErr e)
  let mut docs : List ReqDoc := []
  for dj in docsJ do
    match parseDoc dj with
    | .ok d => docs := docs ++ [d]
    | .error e => throw (jsonErr e)
  let cmdsJ ←
    match getArr j "cmds" with
    | .ok a => pure a
    | .error _ => pure #[]
  let mut cmds : List ReqCmd := []
  for cj in cmdsJ do
    match parseCmd cj with
    | .ok c => cmds := cmds ++ [c]
    | .error e => throw (jsonErr e)
  -- reject before building: a line with an item's shape that does not parse is
  -- an error, not prose
  for d in docs do
    match scanLines d.path.toList 0 d.lines with
    | .ok _    => pure ()
    | .error e => throw (Json.mkObj [("err", lerrJson e)])
  -- build the plan and run the request.  `loadPlan` is the whole loader as one
  -- function, which is what makes `the_kernel_reads_back_what_it_writes` a
  -- theorem about the code the FFI runs rather than about a copy of it.
  match loadPlan docs with
  | .error e   => throw e
  | .ok plan   => runPlan plan cmds


/-- Total: every path returns a `String`.  No `panic!`, no `!`, no `partial`. -/
def call (input : String) : String :=
  match Json.parse input with
  | .error e => Json.compress (jsonErr s!"bad json: {e}")
  | .ok j =>
    match run j with
    | .error e => Json.compress e
    | .ok r    => Json.compress r

@[export tm_kernel_call]
def callExport (input : String) : String := call input

end Tm
