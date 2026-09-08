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
  -- parse every document.  A placement carries its document's horizon, which is
  -- what says which line of a demotion is the tombstone.
  let splits := docs.map (fun d => (splitDoc 0 d.lines, d.reg))
  let places := (splits.zipIdx.map (fun p => placementsOfDoc p.2 p.1.2 p.1.1)).flatten
  let items ←
    match buildEntities places with
    | .ok s => pure s
    | .error e => throw (Json.mkObj [("err", lerrJson e)])
  let store := loadStore items
  let planDocs : List Doc :=
    docs.map (fun d => ⟨d.path.toList, (splitDoc 0 d.lines).prose, d.reg⟩)
  -- the document half is established **by construction**: prose is exactly what
  -- did not parse as an item, so there is no separate validator to drift.
  let hdocs : docsWf ⟨planDocs, store⟩ = true := by
    show List.all planDocs docWf = true
    simp only [planDocs, List.all_eq_true, List.mem_map]
    rintro d ⟨x, _, rfl⟩
    show List.all (splitDoc 0 x.lines).prose (fun q => !isItemLine q.2) = true
    simp only [List.all_eq_true]
    intro q hq
    simp [splitDoc_prose_not_item 0 x.lines q hq]
  -- the other three parts are decidable checks at the boundary, in the same
  -- place and of the same kind as `Grain.ofNat?`.  `pathsDistinct` is the one
  -- that stops two documents claiming one file (Plan.lean); `sitesInRange` and
  -- `demotionsOriented` can only fail on a request whose documents were built
  -- inconsistently with the placements they produced -- `orientPair` establishes
  -- the second one for every entity it builds -- and both are checked rather
  -- than assumed because "cannot happen" is what the shipped `move_to` also
  -- said.  Turning either into a construction needs the same `zipIdx` bound
  -- lemma; that gap is recorded in the README rather than papered over.
  if hpath : pathsDistinct (⟨planDocs, store⟩ : PlanCore) = true then
    if hsites : sitesInRange (⟨planDocs, store⟩ : PlanCore) = true then
      if hor : demotionsOriented (⟨planDocs, store⟩ : PlanCore) = true then
        -- and the item half of the plan-level tier: rank distinctness, `@parent`
        -- and `after:` total and acyclic, §4.2's sections, §4.3's shapes.  Same
        -- discipline, same place; `firstItemFault` names which one failed.
        if hitems : itemsWf (⟨planDocs, store⟩ : PlanCore) = true then
          let plan : WfPlan := ⟨⟨planDocs, store⟩, planWf_of_parts hdocs hsites hpath hor hitems⟩
          runPlan plan cmds
        else
          throw (Json.mkObj [("err", Json.mkObj
            [("itemCheck", Json.str (firstItemFault ⟨planDocs, store⟩))])])
      else
        throw (Json.mkObj [("err", lerrJson (.ambiguousDemotion
          ((firstUnoriented ⟨planDocs, store⟩).getD [])))])
    else
      throw (Json.mkObj [("err", Json.mkObj [("kernel", Json.str "siteOutOfRange")])])
  else
    throw (Json.mkObj [("err", lerrJson (.duplicatePath
      ((firstDupPath (docs.map (fun d => d.path.toList))).getD [])))])


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
