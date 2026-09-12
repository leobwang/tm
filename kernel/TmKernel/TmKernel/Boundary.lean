import TmKernel.Cmd
import TmKernel.Json
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
  /-- two lines of one id, in two files, neither of which is a tombstone:
      `render` writes a second line only as a tombstone, and a tombstone is
      `[-]`.  Nothing renders these two, so they are rejected rather than
      approximated.

      There is no `splitLine` beside this one any more.  It said "two lines of
      one id whose bytes differ", and §6.3's own week close writes exactly
      that — the month copy carries `est:` = remaining and a `demoted:` stamp
      the week line does not.  A tombstone that holds its own bytes renders
      the pair, so the error had nothing left to refuse. -/
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

/-- Build the entity whose record is `live` and whose tombstone is `arch`.
`none` means no entity renders that pair — the caller rejects.

Two things changed with the demotion model.  The tombstone keeps **its own
bytes** (`arch.item`), so a pair whose two lines differ — which is what §6.3's
close writes, `est:` and a stamp on the copy — is representable; and the
record's status is `statusOfGlyph live.glyph`, which is total, so a `[ ]`
record beside a standing archive is read as what it is instead of refused. -/
def pairEntity (arch live : Placement) : Option Entity :=
  match arch.glyph with
  | .demoted =>
    if h : wf ({ live := ⟨live.doc, live.rank⟩,
                 archive := some ⟨⟨arch.doc, arch.rank⟩, arch.item⟩,
                 status := statusOfGlyph live.glyph, line := live.item } : Core) = true
    then some ⟨_, h⟩ else none
  | _ => none

/-- One line on its own: the entity that renders exactly it.  **Total**, and
that is the fix the corpus forced.

It used to reject a lone `[-]`, on the reading that "a demotion is two lines".
§6.3's *week* close does write two, but `tm close month` then carries the
`month/…# Demoted` copy into the next month file and touches nothing else, so a
`# Demoted` section holds `[-]` lines whose partner is in a file the host need
not have handed over — and §4.3's own `month/2026-09.md` is such a file.  The
Rust core agrees: `is_archive_copy` is a predicate on **one** item and a key
group of size one is resolved without looking for a partner.  So `[-]` standing
alone is `Status.demoted`, and every `# Demoted` section in the corpus loads. -/
def loneEntity (q : Placement) : Entity :=
  ⟨{ live := ⟨q.doc, q.rank⟩, archive := none, status := statusOfGlyph q.glyph,
     line := q.item }, rfl⟩

/-- **Which line is the tombstone: the box first, then the files.**

§6.3 gives the archive record two marks and the loader uses them in that order,
because §3.1 stores one of them and derives the other (see `demotionsOriented`,
Plan.lean, for the argument):

* an archive record is `[-]` — the close writes it that way and only
  `tm readopt` reopens a box, and what it reopens is the record.  So a line
  that is not `[-]` is not the tombstone, whichever file it is in.  This
  clause is what reads §4.3's own pair: a `[ ]` in `week/2026-W37.md` beside
  the `[-]` in `month/2026-09.md # Demoted`;
* where both lines are `[-]` — the snapshot straight after a close — the box
  says nothing and the files say it instead: the tombstone stays in the region
  that was **closed** and the record goes to `closeTo`, which is strictly
  after it (`demotion_target_follows_the_closed_region`).

`horizonPrecedes` is antisymmetric, so the second clause has at most one
answer, and neither clause reads the argument order (`orientPair_comm`).
`none` is the genuine ambiguity — two `[-]` lines whose documents declare no
order — and it is reported rather than resolved.  Two lines *neither* of which
is `[-]` is also `none` here; the caller names that one `notADemotion`, which
is what it is. -/
def orientPair (a b : Placement) : Option (Placement × Placement) :=
  match a.glyph == Glyph.demoted, b.glyph == Glyph.demoted with
  | true,  false => some (a, b)
  | false, true  => some (b, a)
  | false, false => none
  | true,  true  =>
    if horizonPrecedes a.region b.region then some (a, b)
    else if horizonPrecedes b.region a.region then some (b, a)
    else none

/-- **The loader's answer is a function of the two lines, not of their order.**
This is the defect this section exists to remove, as a theorem. -/
theorem orientPair_comm (a b : Placement) : orientPair a b = orientPair b a := by
  unfold orientPair
  cases ha : a.glyph == Glyph.demoted <;> cases hb : b.glyph == Glyph.demoted <;>
    simp only [] <;>
    first
      | rfl
      | (by_cases hab : horizonPrecedes a.region b.region = true
         · rw [if_pos hab, if_neg (by simp [horizonPrecedes_asymm hab]), if_pos hab]
         · simp only [Bool.not_eq_true] at hab
           by_cases hba : horizonPrecedes b.region a.region = true
           · rw [if_neg (by simp [hab]), if_pos hba, if_pos hba]
           · simp only [Bool.not_eq_true] at hba
             rw [if_neg (by simp [hab]), if_neg (by simp [hba]), if_neg (by simp [hba]),
               if_neg (by simp [hab])])

/-- What an orientation guarantees: the tombstone is one of the two lines given,
its box is `[-]`, and — **when the record's box is `[-]` too** — the files order
them.  The third conjunct is the one that weakened, and it weakened exactly
where the second is enough on its own. -/
theorem orientPair_cases {a b arch live : Placement} (h : orientPair a b = some (arch, live)) :
    ((arch = a ∧ live = b) ∨ (arch = b ∧ live = a)) ∧
      arch.glyph = Glyph.demoted ∧
      (live.glyph = Glyph.demoted →
        horizonPrecedes arch.region live.region = true) := by
  unfold orientPair at h
  cases ha : a.glyph == Glyph.demoted <;> cases hb : b.glyph == Glyph.demoted <;>
      rw [ha, hb] at h <;> simp only [] at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    refine ⟨Or.inr ⟨rfl, rfl⟩, by simpa using hb, ?_⟩
    intro hc; rw [hc] at ha; simp at ha
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    refine ⟨Or.inl ⟨rfl, rfl⟩, by simpa using ha, ?_⟩
    intro hc; rw [hc] at hb; simp at hb
  · split at h
    · rename_i hab
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2
      exact ⟨Or.inl ⟨rfl, rfl⟩, by simpa using ha, fun _ => hab⟩
    · split at h
      · rename_i hba
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        subst h1; subst h2
        exact ⟨Or.inr ⟨rfl, rfl⟩, by simpa using hb, fun _ => hba⟩
      · simp at h

/-- Two lines of one id: the only entity that renders both is a demotion pair,
and *which* line is the tombstone is settled by `orientPair` — the box, then
the files — before any entity is built.  Anything else is rejected: the two
lines in one file, which is the invariant itself; the pair in which neither
line is `[-]`, which no `render` writes; and the `[-]`/`[-]` pair whose files
do not order it, which the first version silently resolved by argument order.

**`splitLine` is gone from here**, and that is the model change: the two lines
of §6.3's pair are *supposed* to differ — the copy carries `est:` = remaining
and a stamp — and an entity whose tombstone holds its own bytes renders both.
Refusing them was a rule about a model that had one token vector, and it
refused three of the five fixture plans. -/
def pairedEntity (i : Id) (a b : Placement) : Except LErr Entity :=
  if a.doc == b.doc then .error (.dupId i)
  else if a.glyph != Glyph.demoted && b.glyph != Glyph.demoted then .error (.notADemotion i)
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
  have hgl : (b.glyph != Glyph.demoted && a.glyph != Glyph.demoted)
      = (a.glyph != Glyph.demoted && b.glyph != Glyph.demoted) := Bool.and_comm _ _
  unfold pairedEntity
  rw [hdoc, hgl, orientPair_comm b a]

/-- **The ambiguity is named, not resolved.**  Two `[-]` lines of one id whose
documents declare no order between them — two backlog files, one file with no
declared region, two files claiming the same week — are rejected by name.  This
is the `[-]`/`[-]` pair `demote` writes, and the kernel's own output can never
be in this state: `demotionsOriented` is part of `planWf`, so `mapAt` refuses to
produce it (`mapAt_rejects_unoriented`).

The two glyph hypotheses are what the statement gained, and they are exactly
right: with one of the boxes open there is nothing ambiguous about the pair and
the loader reads it without asking a file. -/
theorem unordered_horizons_are_rejected (i : Id) (a b : Placement)
    (hd : a.doc ≠ b.doc) (hga : a.glyph = Glyph.demoted) (hgb : b.glyph = Glyph.demoted)
    (hab : horizonPrecedes a.region b.region = false)
    (hba : horizonPrecedes b.region a.region = false) :
    pairedEntity i a b = .error (.ambiguousDemotion i) := by
  unfold pairedEntity orientPair
  rw [if_neg (by simpa using hd), if_neg (by simp [hga, hgb])]
  simp only [hga, hgb, beq_self_eq_true]
  rw [if_neg (by simp [hab]), if_neg (by simp [hba])]

/-- The whole inverse, for one id's lines. -/
def buildEntity (i : Id) : List Placement → Except LErr Entity
  | [q]    => .ok (loneEntity q)
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

/-- The line a placement was read from: its site, and the bytes `serializeItem`
writes back for the id, box and token vector the parser returned. -/
def placementLine (q : Placement) : Line :=
  ⟨q.id, ⟨q.doc, q.rank⟩, serializeItem q.id q.glyph q.item⟩

theorem lone_placement_renders_back (q : Placement) :
    (loneEntity q).val.live = ⟨q.doc, q.rank⟩ ∧ (loneEntity q).val.line = q.item ∧
      glyphAt (loneEntity q).val (loneEntity q).val.live = q.glyph :=
  ⟨rfl, rfl, glyphAt_statusOfGlyph q.glyph _ _⟩

theorem pairEntity_renders_back (arch live : Placement) (e : Entity)
    (h : pairEntity arch live = some e) :
    e.val.live = ⟨live.doc, live.rank⟩ ∧
      e.val.archive = some ⟨⟨arch.doc, arch.rank⟩, arch.item⟩ ∧
      e.val.line = live.item ∧ arch.glyph = Glyph.demoted ∧
      glyphAt e.val e.val.live = live.glyph ∧
      glyphAt e.val ⟨arch.doc, arch.rank⟩ = Glyph.demoted := by
  unfold pairEntity at h
  split at h
  · rename_i harch
    split at h
    · rename_i hwf
      injection h with h
      subst h
      have hne : (⟨arch.doc, arch.rank⟩ : Site) ≠ ⟨live.doc, live.rank⟩ := by
        intro hc
        simp only [wf_eq, Core.archiveSite, Option.map_some, wfPair_some,
          bne_iff_ne, ne_eq] at hwf
        exact hwf (congrArg Site.doc hc)
      exact ⟨rfl, rfl, rfl, harch,
        glyphAt_statusOfGlyph_paired live.glyph _ _ hne _ _,
        archive_line_is_demoted _ _ rfl⟩
    · simp at h
  · simp at h

/-- **The two-line form §6.3 writes is read back as the entity that wrote it,
and there is exactly one such entity.**  Both boxes come back as they were
found and — this is what the tombstone's own bytes buy — so do both *token
vectors*, so the kernel can round-trip its own output and §4.3's pair, which
the first version could not: it rejected two lines of one id outright, and the
second rejected any pair whose bytes differed.

The orientation is `orientPair a b`, a function of the two lines that is
symmetric in them (`orientPair_comm`), so this conclusion is determinate,
whichever order the host listed the documents in.  What it is a function *of*
changed: the tombstone is the `[-]` line, and only where both lines are `[-]`
is it the line in the closed horizon. -/
theorem paired_placement_renders_back (i : Id) (a b : Placement) (e : Entity)
    (he : pairedEntity i a b = .ok e) :
    ∃ arch live : Placement,
      orientPair a b = some (arch, live) ∧
      (live.glyph = Glyph.demoted → horizonPrecedes arch.region live.region = true) ∧
      e.val.live = ⟨live.doc, live.rank⟩ ∧
      e.val.archive = some ⟨⟨arch.doc, arch.rank⟩, arch.item⟩ ∧
      e.val.line = live.item ∧ arch.glyph = Glyph.demoted ∧
      glyphAt e.val e.val.live = live.glyph ∧
      glyphAt e.val ⟨arch.doc, arch.rank⟩ = Glyph.demoted := by
  unfold pairedEntity at he
  split at he
  · simp at he
  · split at he
    · simp at he
    · split at he
      · simp at he
      · rename_i arch live hor
        split at he
        · rename_i x hx
          injection he with he
          subst he
          obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pairEntity_renders_back arch live x hx
          exact ⟨arch, live, hor, (orientPair_cases hor).2.2, h1, h2, h3, h4, h5, h6⟩
        · simp at he

/-- **The line round trip through the pipeline the FFI actually runs**, for a
line the loader takes on its own.  Parse the bytes, build the entity, ask
`glyphAt` for the box, serialise: the same bytes.  The `[-]` regression is a
counterexample to this statement and not to `serialize_parse`, which is why it
survived. -/
theorem load_render_line (cs : List Char) (i : Id) (g : Glyph) (r : RawItem)
    (k rk : Nat) (reg : Option Region) (e : Entity) (hp : parseItem cs = .ok (i, g, r))
    (he : e = loneEntity ⟨k, rk, i, g, r, reg⟩) :
    serializeItem i (glyphAt e.val e.val.live) e.val.line = cs := by
  subst he
  obtain ⟨_, hline, hglyph⟩ := lone_placement_renders_back ⟨k, rk, i, g, r, reg⟩
  rw [hglyph, hline]
  exact serialize_parse cs i g r hp

/-- **Both lines of a demotion come back as they were found — box *and*
bytes.**  Whichever of the two the loader made the tombstone, each site renders
the box that was in the file at that site and the token vector that was in the
file at that site, so with `serialize_parse` each line is byte-identical to its
input.  This is the statement the one-token-vector entity could not make: it had
to add `a.item = b.item` as a hypothesis, and `pairedEntity` enforced it by
refusing every pair that failed it — which is every pair §6.3's close writes.

`renderCore` is spelled out rather than left as two glyph facts, because the
bytes are the thing the corpus measures. -/
theorem paired_renders_each_placement (i : Id) (a b : Placement) (e : Entity)
    (he : pairedEntity i a b = .ok e) :
    render i e = [⟨i, ⟨a.doc, a.rank⟩, serializeItem i a.glyph a.item⟩,
                  ⟨i, ⟨b.doc, b.rank⟩, serializeItem i b.glyph b.item⟩] ∨
    render i e = [⟨i, ⟨b.doc, b.rank⟩, serializeItem i b.glyph b.item⟩,
                  ⟨i, ⟨a.doc, a.rank⟩, serializeItem i a.glyph a.item⟩] := by
  obtain ⟨arch, live, hor0, _, hlive, harch, hln, hag, hg, hd⟩ :=
    paired_placement_renders_back i a b e he
  have hgl : glyphAt e.val ⟨live.doc, live.rank⟩ = live.glyph := by rw [← hlive]; exact hg
  have hda : glyphAt e.val ⟨arch.doc, arch.rank⟩ = arch.glyph := by rw [hd, hag]
  have hr : render i e = [⟨i, ⟨live.doc, live.rank⟩, serializeItem i live.glyph live.item⟩,
                          ⟨i, ⟨arch.doc, arch.rank⟩, serializeItem i arch.glyph arch.item⟩] := by
    unfold render renderCore
    rw [harch]
    simp only
    rw [hlive, hgl, hln, hda]
  rcases (orientPair_cases hor0).1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2; exact Or.inr hr
  · subst h1; subst h2; exact Or.inl hr

/-! ### Closure: the kernel can read back every pair it writes

The two halves above are about a pair the *host* sent.  This is the other
direction and it is what `demotionsOriented` exists for: take a pair out of an
accepted plan — the two lines it denotes, at the placements it holds them, with
the regions its own documents declare — and hand them back to the loader.  The
loader returns the entity they came from.

That is the sentence "the kernel never writes a demotion it would then have to
guess at", and it is now a theorem rather than an argument.  It is also where
the orientation rule earns the shape it has: the proof splits on whether the
record's box is `[-]`, and takes the horizon from `planWf` only in the branch
where the boxes tie.  In the other branch there is nothing to take. -/

/-- The line a plan denotes at one of an entity's placements, as the loader
would read it back: the site, the box, the bytes, and the region the plan's own
document declares. -/
def placementIn (p : PlanCore) (i : Id) (s : Site) (g : Glyph) (r : RawItem) : Placement :=
  ⟨s.doc, s.rank, i, g, r, docRegion p s.doc⟩

/-- **The kernel can read back every pair it writes.**  For an entity of an
accepted plan that carries a tombstone, `pairedEntity` on the two lines the plan
denotes returns that entity — same record, same tombstone, same bytes at both
sites, same status.

The two `placementIn`s **are** the plan's own two lines: `glyphAt_live` (with
`wf`) says the box at the record is `glyphOfStatus status`, and
`archive_line_is_demoted` says the box at the tombstone is `[-]`; the bytes and
the sites are read straight off `renderCore`, and the regions off the plan's
own documents.

`hpar` is `parent`, the one §3.1 field still stored and still always `none`
(README gap 22): the loader has no way to set it, so it is a hypothesis every
entity the boundary builds satisfies, and the moment `parent` is derived off
the line it disappears.  It is not doing any other work — with a `parent` set,
the loader's answer differs from `e` in exactly that field and in nothing
else. -/
theorem the_kernel_can_read_the_pairs_it_writes (p : WfPlan) (i : Id) (e : Entity) (t : Tomb)
    (hget : p.val.store.get i = some e) (harch : e.val.archive = some t)
    (hpar : e.val.parent = Option.none) :
    pairedEntity i (placementIn p.val i t.site Glyph.demoted t.line)
                   (placementIn p.val i e.val.live (glyphOfStatus e.val.status) e.val.line)
      = .ok e := by
  have hsite : e.val.archiveSite = some t.site := Core.archiveSite_some harch
  have hne : t.site.doc ≠ e.val.live.doc := archive_elsewhere e t.site hsite
  have hcore : ({ live := e.val.live, archive := some ⟨t.site, t.line⟩,
                  status := statusOfGlyph (glyphOfStatus e.val.status),
                  line := e.val.line } : Core) = e.val := by
    rw [statusOfGlyph_glyphOfStatus]
    show ({ live := e.val.live, archive := some t, status := e.val.status,
            line := e.val.line, parent := Option.none } : Core) = e.val
    rw [← harch, ← hpar]
  have hwf : wf ({ live := e.val.live, archive := some ⟨t.site, t.line⟩,
                   status := statusOfGlyph (glyphOfStatus e.val.status),
                   line := e.val.line } : Core) = true := by rw [hcore]; exact e.property
  have hor : orientPair (placementIn p.val i t.site Glyph.demoted t.line)
                        (placementIn p.val i e.val.live (glyphOfStatus e.val.status) e.val.line)
      = some (placementIn p.val i t.site Glyph.demoted t.line,
              placementIn p.val i e.val.live (glyphOfStatus e.val.status) e.val.line) := by
    unfold orientPair placementIn
    simp only [beq_self_eq_true]
    cases hg : glyphOfStatus e.val.status == Glyph.demoted
    · rfl
    · simp only []
      rw [if_pos (the_tombstone_is_behind_the_live_line p i e t.site hget hsite (by simpa using hg))]
  unfold pairedEntity
  rw [if_neg (by simpa [placementIn] using hne), if_neg (by simp [placementIn]), hor]
  unfold pairEntity placementIn
  simp only
  rw [dif_pos hwf]
  have hent : (⟨_, hwf⟩ : Entity) = e := Subtype.ext hcore
  rw [hent]

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


/-! ## JSON — every field read through `jget`, over the `JVal` `jparse` built -/

def jsonErr (s : String) : JVal := jone "err" (.str s.toList)
def getStr (j : JVal) (k : String) : Except String (List Char) := do
  match ← jget j k with
  | some (.str s) => return s | some _ => throw "String expected"
  | none => throw s!"property not found: {k}"

def getNat (j : JVal) (k : String) : Except String Nat := do
  match ← jget j k with
  | some (.num n) => return n | some _ => throw "Natural number expected"
  | none => throw s!"property not found: {k}"

def getArr (j : JVal) (k : String) : Except String (List JVal) := do
  match ← jget j k with
  | some (.arr xs) => return xs | some _ => throw "array expected"
  | none => throw s!"property not found: {k}"

/-- Every element a string, or the request is refused — never a skipped line. -/
def strLines (xs : List JVal) : Except String (List (List Char)) :=
  xs.mapM (fun x => match x with | .str s => .ok s | _ => .error "String expected")

structure ReqDoc where
  path  : String
  reg   : Option Region
  lines : List (List Char)

def parseRegion (j : JVal) : Except String (Option Region) := do
  -- Absent or `null` is no region; a duplicate is `jget`'s refusal, never `none`.
  match ← jget j "grain" with
  | none | some .null => return none
  | some gv =>
      let gn ← match gv with | .num n => pure n | _ => throw "Natural number expected"
      match Grain.ofNat? gn with
      | none   => throw s!"grain {gn} out of range (0..{grainCount - 1})"
      | some g =>
        let ix ← getNat j "ix"
        return some ⟨g, ix⟩

def parseDoc (j : JVal) : Except String ReqDoc := do
  let path ← getStr j "path"
  let reg ← parseRegion j
  let lines ← strLines (← getArr j "lines")
  return ⟨String.ofList path, reg, lines⟩

/-- One command as the UI sends it. -/
inductive ReqCmd
  | move (i : Id) (doc : DocIx)
  | drop (i : Id)
  | est  (i : Id) (v : Nat)
  | demote (i : Id) (doc : DocIx) (stamp : Field.Stamp)
  | readopt (i : Id) (doc : DocIx)
  | rank (i : Id) (n : Nat)
  /-- `tm add`.  The **seed** is supplied by the host — Lean has no randomness
      — and `freshId` (L21) turns it plus the store's domain into an id no item
      claims; freshness is a theorem, not a retry.  The title is plain text: a
      newline, a tab, a `^`, or a title of only spaces is refused at the parser
      with a named message rather than rendering bytes no loader can take back. -/
  | add (seed : Nat) (doc : DocIx) (title : List Char)
  /-- `tm edit ^id <key>=<value>`, keyed.  The payload is already parsed and
      bounded: `parseCmd` runs the key's own field grammar (`editValOf`), so a
      raw value string never rides past the boundary. -/
  | edit (i : Id) (v : EditVal)
  /-- `tm edit ^id <key>=` — unset.  The key carries its exposure proof. -/
  | unset (i : Id) (k : EditKey)
  deriving DecidableEq

/-- §6.3 stamps a demotion with the grain of the horizon that closed — `W37`
from a week close, `D07` from a day close — and a `Field.Stamp` carries which.
The wire sends the period number; the optional `grain` says the letter, and a
request that omits it means a week, which is the close §6.3 attaches a
`demoted:` stamp to.  A `grain` carried twice is refused (`jget`). -/
def stampOf (j : JVal) (n : Nat) : Except String Field.Stamp := do
  match ← jget j "grain" with
  | some (.str g) => return if g == ['d'] then .day n else .week n
  | _             => return .week n

def parseCmd (j : JVal) : Except String ReqCmd := do
  let op ← getStr j "op"
  match String.ofList op with
  | "move" => return .move (← getStr j "id") (← getNat j "doc")
  | "drop" => return .drop (← getStr j "id")
  | "est"  => return .est (← getStr j "id") (← getNat j "min")
  | "demote" =>
    return .demote (← getStr j "id") (← getNat j "doc") (← stampOf j (← getNat j "period"))
  | "readopt" => return .readopt (← getStr j "id") (← getNat j "doc")
  | "rank" => return .rank (← getStr j "id") (← getNat j "rank")
  | "add" =>
    -- The title arrives as the `List Char` `jparse` decoded: no `String` hop.
    let cs ← getStr j "title"
    -- Gap 32's discipline at the parser: the title becomes item tokens, so a
    -- newline would split the line, a tab is not a separator this kernel can
    -- read, and a `^` in the title would read back as a second id (`manyIds`).
    -- The loader must never pick between two readings (§5.6), so these are
    -- refused by name rather than laundered into tokens.  The checks run on
    -- the `List Char` reading the command actually carries.
    if '\n' ∈ cs then throw "titleNewline"
    if '\t' ∈ cs then throw "titleTab"
    if '^' ∈ cs then throw "titleId"
    if cs.all (fun c => c == ' ') then throw "titleBlank"
    -- A leading or trailing space would ride into the token vector as a token
    -- whose word is empty (or keeps the space), and the rendered line would
    -- re-tokenize differently than it was built — the loader must read back
    -- exactly what the command wrote, so the title must be trimmed by the host.
    if cs.head? == some ' ' || cs.getLast? == some ' ' then throw "titleEdge"
    return .add (← getNat j "seed") (← getNat j "doc") cs
  | "edit" =>
    -- The keyed edit.  §5.7: three refusals, each named — a spelling that is
    -- not a key at all (`unknownKey`), a key the edit path is not wired for
    -- yet (`keyNotWired`, README gap 40 names them), and a value the key's
    -- own field grammar refuses (`badValue`).  An empty value is the unset
    -- form, `tm edit ^id <key>=`.
    let i ← getStr j "id"
    let ks ← getStr j "key"
    let vs ← getStr j "value"
    match Field.Key.ofName? ks with
    | none => throw s!"unknownKey {String.ofList ks}"
    | some k =>
      if h : keyEditable k = true then
        if vs.isEmpty then
          return .unset i ⟨k, h⟩
        else
          match editValOf k vs with
          | some v => return .edit i v
          | none   => throw s!"badValue {String.ofList ks}"
      else throw s!"keyNotWired {String.ofList ks}"
  | _ => throw s!"unknown op {String.ofList op}"

def kerrName : KErr → String
  | .occupied       => "occupied"
  | .noSuchId       => "noSuchId"
  | .notDemoted     => "notDemoted"
  | .alreadyDemoted => "alreadyDemoted"
  | .badHorizon     => "badHorizon"
  | .badItem        => "badItem"
  | .tabbedLine     => "tabbedLine"
  | .keyAbsent      => "keyAbsent"

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

/-- `tm add`'s token vector.  Words tokenize exactly as the loader would
tokenize the file line later — the one representation, seen from the command
side.  The head token's separator is forced to a single space because
`serializeItem`'s prefix ends at `]` and the first token supplies the gap that
the fixture style `- [ ] 5 6b … ^m1` writes; the id token's word is `'^' :: i`
so a later load reads back the store key exactly (§5.3's one-reader rule, seen
from the other end). -/
def addTitleToks (title : List Char) (i : Id) : List Tok :=
  match tokenize title with
  | []      => [{ sep := [' '], word := '^' :: i }]
  | t :: ts => { t with sep := [' '] } :: ts ++ [{ sep := [' '], word := '^' :: i }]

/-- The `Core` a fresh `add` writes: open in the resolved destination at
`freshRank`, no tombstone, `live free` (the `[ ]` box), `parent none` like every
line the kernel writes until gap 22 lands. -/
def addCore (p : PlanCore) (dd : Dest p) (i : Id) (title : List Char) : Core :=
  { live := dd.site (freshRank p dd.ix), archive := none, status := .live .free,
    line := { indent := [], toks := addTitleToks title i }, parent := none }

/-- `wf` of an `add`'s core is `wfPair _ none`: there is no tombstone to be in
the wrong file.  The freshness argument is elsewhere — L21 for the id,
`freshRank_gt` for the rank, and `insertFresh`'s `planWf` re-check for the rest. -/
def addEntity (p : PlanCore) (dd : Dest p) (i : Id) (title : List Char) : Entity :=
  ⟨addCore p dd i title, by unfold wf Core.archiveSite; exact wfPair_none _⟩

/-- L21's freshness, restated in the shape `Store.insertFresh` demands.  The
store already answers for itself: an id outside `dom` has no entry, because
`domSpec` makes membership and a `some` answer the same statement. -/
theorem store_get_isNone_of_not_mem {p : PlanCore} {i : Id} (h : i ∉ p.store.dom) :
    (p.store.get i).isNone = true := by
  rcases hget : p.store.get i with _ | e
  · simp [hget]
  · have hsome : (p.store.get i).isSome = true := by simp [hget]
    exact absurd ((p.store.domSpec i).mpr hsome) h

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
  | .demote i d st =>
    match resolveDest p.val d with
    | .error k => .error k
    | .ok dd   => cmdDemote i (freshRank p.val dd.ix) st p dd
  | .readopt i d    =>
    match resolveDest p.val d with
    | .error k => .error k
    | .ok dd   => cmdReadopt i (freshRank p.val dd.ix) p dd
  | .rank i n       => cmdRank i n p
  | .edit i v       => cmdEdit v i p
  | .unset i k      => cmdUnset k i p
  | .add seed d title =>
    match resolveDest p.val d with
    | .error k => .error k
    | .ok dd =>
      p.insertFresh (freshId seed p.val.store.dom)
        (addEntity p.val dd (freshId seed p.val.store.dom) title)
        (store_get_isNone_of_not_mem (add_assigns_a_fresh_id seed _))

/-- **Error 2, as a theorem.**  A destination that is not a document is
rejected, and the plan is untouched. -/
theorem move_to_a_document_that_does_not_exist_is_rejected (p : WfPlan) (i : Id) (n : Nat)
    (h : ¬ n < p.val.docs.length) : applyCmd (.move i n) p = .error .badHorizon := by
  simp [applyCmd, resolveDest, h]

theorem demote_to_a_document_that_does_not_exist_is_rejected (p : WfPlan) (i : Id) (n : Nat)
    (st : Field.Stamp)
    (h : ¬ n < p.val.docs.length) : applyCmd (.demote i n st) p = .error .badHorizon := by
  simp [applyCmd, resolveDest, h]

/-! ### What an `add` does — acceptance, and the check that bites -/

theorem WfPlan.insertFresh_rejects (p : WfPlan) (i : Id) (e : Entity)
    (hfresh : (p.val.store.get i).isNone = true)
    (h : planWf { p.val with store := p.val.store.insertFresh i e hfresh } = false) :
    p.insertFresh i e hfresh = .error .badItem := by
  simp [WfPlan.insertFresh, h]

/-- The wire form refuses a title that would not read back as the item it
pretends to be.  These refusals live in `parseCmd` — the `Except String` path,
so the host's `match` sees the free-text `{"err":"…"}`, not a kernel name —
because each names a different reason the bytes would lie about the plan. -/
theorem parseCmd_rejects_add_title_variants :
    parseCmd (.obj [("op".toList, .str "add".toList), ("seed".toList, .num 7),
        ("doc".toList, .num 0), ("title".toList, .str "a\nb".toList)]) = .error "titleNewline" ∧
    parseCmd (.obj [("op".toList, .str "add".toList), ("seed".toList, .num 7),
        ("doc".toList, .num 0), ("title".toList, .str "a\tb".toList)]) = .error "titleTab" ∧
    parseCmd (.obj [("op".toList, .str "add".toList), ("seed".toList, .num 7),
        ("doc".toList, .num 0), ("title".toList, .str "steal ^m1".toList)]) = .error "titleId" ∧
    parseCmd (.obj [("op".toList, .str "add".toList), ("seed".toList, .num 7),
        ("doc".toList, .num 0), ("title".toList, .str "".toList)]) = .error "titleBlank" ∧
    parseCmd (.obj [("op".toList, .str "add".toList), ("seed".toList, .num 7),
        ("doc".toList, .num 0), ("title".toList, .str " padded ".toList)]) = .error "titleEdge" :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **`add` inserts.**  Whenever the command succeeds, the store of the
post-state holds the new entity under exactly the id L21's `freshId` names. -/
theorem cmdAdd_inserts (p : WfPlan) (seed : Nat) (n : Nat) (title : List Char)
    (q : WfPlan) (hq : applyCmd (.add seed n title) p = .ok q) :
    (q.val.store.get (freshId seed p.val.store.dom)).isSome = true := by
  cases hd : resolveDest p.val n with
  | error k =>
      simp only [applyCmd, hd] at hq
      exact absurd hq (by simp)
  | ok dd =>
      simp only [applyCmd, hd] at hq
      have hget := WfPlan.insertFresh_get p _ _ _ _ hq
      rw [hget]; simp

/-- **`add` lands at `freshRank`** — the one rank that beats every line already
in the file.  This is what says a second `add` into the same document does not
collide with the first: the first is a line of the file the second's
`freshRank_gt` sees.  The entity arrives as an extra argument because the wire
carries an id, not a rank; `cmdAdd_inserts` says that id names something here. -/
theorem cmdAdd_rank (p : WfPlan) (seed : Nat) (n : Nat) (title : List Char)
    (q : WfPlan) (e : Entity) (hq : applyCmd (.add seed n title) p = .ok q)
    (he : q.val.store.get (freshId seed p.val.store.dom) = some e) :
    e.val.live = ⟨n, freshRank p.val n⟩ := by
  cases hd : resolveDest p.val n with
  | error k =>
      simp only [applyCmd, hd] at hq
      exact absurd hq (by simp)
  | ok dd =>
      simp only [applyCmd, hd] at hq
      have hget := WfPlan.insertFresh_get p _ _ _ _ hq
      rw [hget] at he
      cases he
      simp [addEntity, addCore, Dest.site, resolveDest_ix hd]

/-- **`add` touches nothing else.**  Every other id keeps its entity exactly. -/
theorem cmdAdd_other_untouched (p : WfPlan) (seed : Nat) (n : Nat) (title : List Char)
    (q : WfPlan) (hq : applyCmd (.add seed n title) p = .ok q) (j : Id)
    (hij : freshId seed p.val.store.dom ≠ j) :
    q.val.store.get j = p.val.store.get j := by
  cases hd : resolveDest p.val n with
  | error k =>
      simp only [applyCmd, hd] at hq
      exact absurd hq (by simp)
  | ok dd =>
      simp only [applyCmd, hd] at hq
      exact WfPlan.insertFresh_other p _ j _ _ _ hq
        (fun hji => absurd hji.symm hij)

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

def lerrJson : LErr → JVal
  | .dupId i          => jone "dupId" (.str i)
  | .notADemotion i   => jone "notADemotion" (.str i)
  | .ambiguousDemotion i => jone "ambiguousDemotion" (.str i)
  | .duplicatePath pa => jone "duplicatePath" (.str pa)
  | .badLine pa n w   => jone "badLine" (.obj
      [("path".toList, .str pa), ("line".toList, .num n), ("why".toList, .str (toString (repr w)).toList)])

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
def regionJson (r : Option Region) : List (List Char × JVal) :=
  match r with
  | none   => []
  | some g => [("grain".toList, .num g.grain.val), ("ix".toList, .num g.ix)]

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
          simp only [pure, Except.pure] at h
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

theorem loneEntity_archive (q : Placement) : (loneEntity q).val.archive = none := rfl

theorem buildEntity_renders (i : Id) (qs : List Placement) (e : Entity)
    (hid : ∀ q ∈ qs, q.id = i) (h : buildEntity i qs = .ok e) (l : Line) :
    l ∈ render i e ↔ ∃ q ∈ qs, l = placementLine q := by
  match qs with
  | [] => simp [buildEntity] at h
  | [q] =>
      have h' : e = loneEntity q := by
        have : Except.ok (loneEntity q) = (.ok e : Except LErr Entity) := h
        injection this with this; exact this.symm
      subst h'
      have hq : q.id = i := hid q (by simp)
      obtain ⟨hlive, hline, hglyph⟩ := lone_placement_renders_back q
      have harch := loneEntity_archive q
      have hr : render i (loneEntity q) = [placementLine q] := by
        unfold render renderCore placementLine
        simp only [harch]
        rw [hglyph, hline, hlive, hq]
      rw [hr]
      simp
  | [a, b] =>
      have h' : pairedEntity i a b = .ok e := h
      have ha : a.id = i := hid a (by simp)
      have hb : b.id = i := hid b (by simp)
      obtain ⟨arch, live, hor, _, hlive, harch, hline, hag, hg, hd⟩ :=
        paired_placement_renders_back i a b e h'
      have hcases := (orientPair_cases hor).1
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
        rw [hd, hg, hline, hlive, hLid, hAid, hag]
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
def loadPlan (docs : List ReqDoc) : Except JVal WfPlan :=
  match buildEntities (placementsOf 0 docs) with
  | .error e => .error (jone "err" (lerrJson e))
  | .ok items =>
    if hpath : pathsDistinct (loadCore docs items) = true then
      if hsites : sitesInRange (loadCore docs items) = true then
        if hor : demotionsOriented (loadCore docs items) = true then
          if hitems : itemsWf (loadCore docs items) = true then
            .ok ⟨loadCore docs items,
              planWf_of_parts (loadCore_docsWf docs items) hsites hpath hor hitems⟩
          else
            .error (jone "err"
              (jone "itemCheck" (.str (firstItemFault (loadCore docs items)).toList)))
        else
          .error (jone "err" (lerrJson (.ambiguousDemotion
            ((firstUnoriented (loadCore docs items)).getD []))))
      else
        .error (jone "err" (jone "kernel" (.str "siteOutOfRange".toList)))
    else
      .error (jone "err" (lerrJson (.duplicatePath
        ((firstDupPath (docs.map (fun d => d.path.toList))).getD []))))

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

/-- The plan holds exactly the request's documents, in the request's order — so
the response has one entry per request document and they line up. -/
theorem loadPlan_docs (docs : List ReqDoc) (p : WfPlan) (h : loadPlan docs = .ok p) :
    p.val.docs = docs.map mkDoc := by
  obtain ⟨items, _, hval⟩ := loadPlan_spec docs p h
  rw [hval]
  rfl

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

/-! ### A command rewrites only the files it touches

The round trip above is about a plan the loader just built.  The other half of
"the kernel reads back what it writes" is about a plan a *command* produced: the
response carries every document, so a `demote` in `week/` re-renders `month/`,
`backlog.md` and every other file too, and nothing said those came back
unchanged.  `lines_set` says it in one line — the two line lists differ in one
contiguous block — so a document neither the old nor the new entity has a line
in renders identically. -/

theorem renderDocAt_untouched (p : PlanCore) (i : Id) (e e' : Entity)
    (hs : (p.store.get i).isSome = true) (hget : p.store.get i = some e)
    (k : DocIx) (d : Doc)
    (hold : ∀ l ∈ render i e, l.site.doc ≠ k)
    (hnew : ∀ l ∈ render i e', l.site.doc ≠ k) :
    renderDocAt { p with store := p.store.set i e' hs } k d = renderDocAt p k d := by
  obtain ⟨A, C, hp, hp', _, _⟩ := lines_set p i e e' hs hget
  have hfe : (render i e).filter (fun l => l.site.doc == k) = [] :=
    List.filter_eq_nil_iff.2 (fun l hl => by simpa using hold l hl)
  have hfe' : (render i e').filter (fun l => l.site.doc == k) = [] :=
    List.filter_eq_nil_iff.2 (fun l hl => by simpa using hnew l hl)
  unfold renderDocAt
  rw [hp', hp]
  simp only [List.filter_append, hfe, hfe', List.nil_append]

/-- The post-state of `mapAt`, in the shape the lemmas above want: the same
`docs`, and the store with exactly one entity replaced. -/
theorem mapAt_ok_shape (p q : WfPlan) (i : Id) (f : Entity → Except KErr Entity)
    (hq : p.mapAt i f = .ok q) :
    ∃ (e e' : Entity) (hs : (p.val.store.get i).isSome = true),
      p.val.store.get i = some e ∧ f e = .ok e' ∧
      q.val = { p.val with store := p.val.store.set i e' hs } := by
  unfold WfPlan.mapAt at hq
  split at hq
  · simp at hq
  · rename_i e hget
    split at hq
    · simp at hq
    · rename_i e' hf
      split at hq
      · injection hq with hq
        exact ⟨e, e', by simp [hget], hget, hf, by rw [← hq]⟩
      · simp at hq

/-- **A command's output is byte-identical in every file it does not touch.**
This is the other leg of `the_kernel_reads_back_what_it_writes`: not only does
the kernel accept its own output, it does not perturb the files it had no
business perturbing. -/
theorem a_command_rewrites_only_the_files_it_touches (p q : WfPlan) (i : Id)
    (f : Entity → Except KErr Entity) (e e' : Entity) (hq : p.mapAt i f = .ok q)
    (hget : p.val.store.get i = some e) (hget' : q.val.store.get i = some e')
    (k : DocIx) (d : Doc)
    (hold : ∀ l ∈ render i e, l.site.doc ≠ k)
    (hnew : ∀ l ∈ render i e', l.site.doc ≠ k) :
    renderDocAt q.val k d = renderDocAt p.val k d := by
  obtain ⟨e₀, e₀', hs, hg₀, _, hshape⟩ := mapAt_ok_shape p q i f hq
  have he : e₀ = e := Option.some.inj (hg₀.symm.trans hget)
  have he' : e₀' = e' := by
    have h1 : q.val.store.get i = some e₀' := by
      rw [hshape]
      exact Store.get_set_self p.val.store i e₀' hs
    exact Option.some.inj (h1.symm.trans hget')
  subst he
  subst he'
  rw [hshape]
  exact renderDocAt_untouched p.val i e₀ e₀' hs hg₀ k d hold hnew

/-! ### The rank verb's laws (L20a, L20b)

They live here rather than beside `cmdRank` (Cmd.lean) for one mechanical
reason: both read a successful `cmdRank` through `mapAt_ok_shape`, and the open
chain `Plan ← Cmd ← Boundary` will not bend backwards. -/

/-- **L20a (P\*).**  `tm rank ^id n` is idempotent: ranking a line where it
already is changes nothing, so the verb cannot be a source of spurious diffs.
The proof is three no-ops stacked: the second `setRankE` re-derives the entity
it was given (`setRankE_idem`), the store write-back of a found entity is the
identity (`Store.set_same`), and `mapAt` then returns the very `WfPlan` it got. -/
theorem rank_is_idempotent (i : Id) (n : Nat) (p q : WfPlan)
    (h : cmdRank i n p = .ok q) : cmdRank i n q = .ok q := by
  obtain ⟨pe, pe', hs, hget, hfe, hshape⟩ := mapAt_ok_shape p q i (setRankE n) h
  have hqe : q.val.store.get i = some pe' := by
    rw [hshape]
    exact Store.get_set_self p.val.store i pe' hs
  have hide : setRankE n pe' = .ok pe' := setRankE_idem n pe pe' hfe
  have hcs : {q.val with store := q.val.store.set i pe' (by rw [hqe]; rfl)} = q.val :=
    planCore_set_same hqe
  have hq : planWf {q.val with store := q.val.store.set i pe' (by rw [hqe]; rfl)} = true := by
    rw [hcs]; exact q.property
  unfold cmdRank
  refine (mapAt_at (p := q) (f := setRankE n) (e := pe') (e' := pe') (hq := hq) hqe hide).trans ?_
  refine congrArg Except.ok ?_
  apply Subtype.ext
  exact hcs

/-- **L20b (P\*).**  `tm rank` is order-preserving on everything it did not
name: two other items sharing a document keep their relative order.  §7.4's
sort key is `(p, root_line_order, own_line_order)`, so a rank command that
renumbered the others would silently reshuffle the plan for items the user
never touched.  Structurally the risk is nil here — `mapAt` writes exactly one
store slot and both other entities read back unchanged — which is *why* the
proof is `Store.get_set_other` twice rather than an induction over renumbers.
(`hdoc` is deliberately not discharged from: the order in fact survives even
when the two others sit in *different* files, but the law as stated in plan
§3.3 — §7.4's tie-break is per-file — claims the weaker thing, and the weaker
claim is the one the plan asked for.) -/
theorem rank_preserves_the_order_of_the_others (i : Id) (n : Nat) (p q : WfPlan)
    (j k : Id) (hj : j ≠ i) (hk : k ≠ i) (ej ek fj fk : Entity)
    (hjp : p.val.store.get j = some ej) (hkp : p.val.store.get k = some ek)
    (hjq : q.val.store.get j = some fj) (hkq : q.val.store.get k = some fk)
    (h : cmdRank i n p = .ok q)
    (hdoc : ej.val.live.doc = ek.val.live.doc)
    (hlt : ej.val.live.rank < ek.val.live.rank) :
    fj.val.live.rank < fk.val.live.rank := by
  obtain ⟨e, e', hs, hget, hfe, hshape⟩ := mapAt_ok_shape p q i (setRankE n) h
  have hjq' : q.val.store.get j = p.val.store.get j := by
    rw [hshape]
    exact Store.get_set_other _ _ _ _ hs hj
  have hkq' : q.val.store.get k = p.val.store.get k := by
    rw [hshape]
    exact Store.get_set_other _ _ _ _ hs hk
  rw [hjq', hjp] at hjq
  rw [hkq', hkp] at hkq
  have hej : ej = fj := Option.some.inj hjq
  have hek : ek = fk := Option.some.inj hkq
  rw [← hej, ← hek]
  exact hlt

/-! ## `Normalized` after a command: discharged, not hoped for

`mapAt` re-establishes `planWf` by computation on every post-state, and rank
distinctness is one of its conjuncts.  That made `mapAt_ok_of_inRange` and
`cmdMove_succeeds` (Cmd.lean) each carry an `itemsWf` hypothesis about the
post-state: the boundary always relocates to `freshRank`, and `freshRank_gt`
proves that rank is above every rank already in the destination, but the step
from there to "and so the post-state is still `Normalized`" was not written.
That was README gap 11, and the check it left standing was one no proof could
be shown to pass — the shape of trapdoor this kernel exists to remove.

The step is written here.  `lines_set` and `normalized_set` (Plan.lean) supply
the general lemma; what is left is the arithmetic — `freshRank` beats every
prose rank as well as every line rank — and the observation that **every command
either lands on the fresh rank or re-uses a site the entity already had**, so
one hypothesis covers `move`, `demote`, `readopt`, `drop` and `est` together.

What is *not* discharged, and stays a hypothesis, is the rest of `itemsWf`:
a move into a day file outside `# Pinned` breaks `sectionsWf` and a move into
`month/` can break `shapesWf`.  Those are real refusals, not gaps. -/

theorem foldl_max_ge_gen {α : Type} (f : α → Nat) : ∀ (xs : List α) (a : Nat),
    a ≤ xs.foldl (fun acc y => Nat.max acc (f y)) a := by
  intro xs
  induction xs with
  | nil => intro a; exact Nat.le_refl a
  | cons x t ih => intro a; exact Nat.le_trans (Nat.le_max_left a (f x)) (ih _)

theorem le_foldl_max_gen {α : Type} (f : α → Nat) (x : α) : ∀ (xs : List α) (a : Nat),
    x ∈ xs → f x ≤ xs.foldl (fun acc y => Nat.max acc (f y)) a := by
  intro xs
  induction xs with
  | nil => intro a h; simp at h
  | cons y t ih =>
      intro a h
      simp only [List.foldl_cons]
      rcases List.mem_cons.1 h with hh | hh
      · rw [hh]
        exact Nat.le_trans (Nat.le_max_right a (f y)) (foldl_max_ge_gen f t _)
      · exact ih _ hh

/-- **`freshRank` beats the prose too.**  `freshRank_gt` covers the item lines;
this is the other half, and without it a relocated line could land on a heading's
rank, which `Normalized` counts in the same list. -/
theorem docProseMax_ge (p : PlanCore) (k : DocIx) (d : Doc) (hd : p.docs[k]? = some d)
    (q : Nat × List Char) (hq : q ∈ d.prose) : q.1 ≤ docProseMax p k := by
  unfold docProseMax
  rw [hd]
  exact le_foldl_max_gen Prod.fst q d.prose 0 hq

theorem archive_line_mem (i : Id) (e : Entity) (t : Tomb) (h : e.val.archive = some t) :
    ∃ m ∈ render i e, m.site = t.site := by
  refine ⟨⟨i, t.site, serializeItem i (glyphAt e.val t.site) t.line⟩, ?_, rfl⟩
  unfold render renderCore
  rw [h]
  simp

theorem live_line_site_mem (i : Id) (e : Entity) : ∃ m ∈ render i e, m.site = e.val.live := by
  refine ⟨⟨i, e.val.live, serializeItem i (glyphAt e.val e.val.live) e.val.line⟩, ?_, rfl⟩
  unfold render renderCore
  simp

/-- **The one hypothesis every command satisfies**: each line of the new entity
sits either on the fresh rank in the destination, or on a site the entity
already occupied.  `SitesFree` follows, and with it `Normalized`. -/
theorem normalized_of_fresh_or_old (p : WfPlan) (i : Id) (e a : Entity) (k : DocIx)
    (hs : (p.val.store.get i).isSome = true) (hget : p.val.store.get i = some e)
    (hsites : ∀ l ∈ render i a,
       l.site = ⟨k, freshRank p.val k⟩ ∨ ∃ m ∈ render i e, m.site = l.site) :
    normalized { p.val with store := p.val.store.set i a hs } = true := by
  refine normalized_set p.val i e a hs hget (itemsWf_parts p.items).1 ?_
  intro l hl
  rcases hsites l hl with hfresh | ⟨m0, hm0, hm0s⟩
  · have hdoc : l.site.doc = k := by rw [hfresh]
    have hrank : l.site.rank = freshRank p.val k := by rw [hfresh]
    constructor
    · intro m hm hsite
      exfalso
      have h1 : m.site.doc = k := by rw [hsite, hdoc]
      have h2 : m.site.rank = freshRank p.val k := by rw [hsite, hrank]
      have := freshRank_gt p.val k m hm h1
      omega
    · intro d hd q hq
      rw [hdoc] at hd
      have h1 := docProseMax_ge p.val k d hd q hq
      have h2 : docProseMax p.val k < freshRank p.val k :=
        Nat.lt_succ_of_le (Nat.le_max_left _ _)
      rw [hrank]
      omega
  · have hm0l : m0 ∈ p.val.lines := mem_lines_of_render p.val i e m0 hget hm0
    constructor
    · intro m hm hsite
      have : m = m0 := site_names_one_line p m m0 hm hm0l (by rw [hsite, hm0s])
      rw [this]
      exact hm0
    · intro d hd q hq
      have hd' : p.val.docs[m0.site.doc]? = some d := by rw [hm0s]; exact hd
      have := no_prose_line_shares_a_rank p m0 hm0l d hd' q hq
      rw [hm0s] at this
      exact this

/-- A relocation: the live line goes to the fresh rank, and any tombstone the
new entity carries is one the old entity already had a line at. -/
theorem normalized_after_relocation (p : WfPlan) (i : Id) (e a : Entity) (k : DocIx)
    (hs : (p.val.store.get i).isSome = true) (hget : p.val.store.get i = some e)
    (hlive : a.val.live = ⟨k, freshRank p.val k⟩)
    (harch : ∀ t, a.val.archive = some t → ∃ m ∈ render i e, m.site = t.site) :
    normalized { p.val with store := p.val.store.set i a hs } = true := by
  refine normalized_of_fresh_or_old p i e a k hs hget ?_
  intro l hl
  rcases render_site i a l hl with h | h
  · exact Or.inl (by rw [h, hlive])
  · cases ht : a.val.archive with
    | none => rw [Core.archiveSite_none ht] at h; simp at h
    | some t =>
        rw [Core.archiveSite_some ht] at h
        obtain ⟨m, hm, hms⟩ := harch t ht
        exact Or.inr ⟨m, hm, by rw [hms, Option.some.inj h]⟩

/-- An edit that moves nothing: both placements are where they were, so there is
nothing to check at all.  This is `drop` and `est`. -/
theorem normalized_after_edit (p : WfPlan) (i : Id) (e a : Entity)
    (hs : (p.val.store.get i).isSome = true) (hget : p.val.store.get i = some e)
    (hlive : a.val.live = e.val.live) (harch : a.val.archive = e.val.archive) :
    normalized { p.val with store := p.val.store.set i a hs } = true := by
  refine normalized_of_fresh_or_old p i e a 0 hs hget ?_
  intro l hl
  refine Or.inr ?_
  rcases render_site i a l hl with h | h
  · rw [h, hlive]; exact live_line_site_mem i e
  · cases ht : a.val.archive with
    | none => rw [Core.archiveSite_none ht] at h; simp at h
    | some t =>
        rw [Core.archiveSite_some ht] at h
        obtain ⟨m, hm, hms⟩ := archive_line_mem i e t (by rw [← harch]; exact ht)
        exact ⟨m, hm, by rw [hms, Option.some.inj h]⟩

/-- **`move` at the boundary's own rank keeps ranks distinct.** -/
theorem move_at_freshRank_normalized (p : WfPlan) (i : Id) (e a : Entity) (k : DocIx)
    (hs : (p.val.store.get i).isSome = true) (hget : p.val.store.get i = some e)
    (hva : a.val = { e.val with live := ⟨k, freshRank p.val k⟩ }) :
    normalized { p.val with store := p.val.store.set i a hs } = true := by
  refine normalized_after_relocation p i e a k hs hget (by rw [hva]) ?_
  intro t hr
  rw [hva] at hr
  exact archive_line_mem i e t hr

theorem moveTo_freshRank_normalized (p : WfPlan) (i : Id) (e a : Entity) (k : DocIx)
    (hs : (p.val.store.get i).isSome = true) (hget : p.val.store.get i = some e)
    (ha : moveTo ⟨k, freshRank p.val k⟩ e = .ok a) :
    normalized { p.val with store := p.val.store.set i a hs } = true :=
  move_at_freshRank_normalized p i e a k hs hget (lift_roundtrips _ _ ha)

/-- **`demote` too** — and here the tombstone is the line the item is leaving,
which is precisely a site the old entity occupied. -/
theorem demote_at_freshRank_normalized (p : WfPlan) (i : Id) (e a : Entity) (k : Nat)
    (st : Field.Stamp)
    (hs : (p.val.store.get i).isSome = true) (hget : p.val.store.get i = some e)
    (ha : demote ⟨k, freshRank p.val k⟩ st e = .ok a) :
    normalized { p.val with store := p.val.store.set i a hs } = true := by
  have hv := demote_roundtrips _ _ _ _ ha
  refine normalized_after_relocation p i e a k hs hget (by rw [hv]) ?_
  intro t hr
  rw [hv] at hr
  have hh : (some ⟨e.val.live, e.val.line⟩ : Option Tomb) = some t := hr
  rw [← Option.some.inj hh]
  exact live_line_site_mem i e

/-- **And `readopt`**, which consumes the tombstone, so it has one line and it
is fresh. -/
theorem readopt_at_freshRank_normalized (p : WfPlan) (i : Id) (e a : Entity) (k : DocIx)
    (hs : (p.val.store.get i).isSome = true) (hget : p.val.store.get i = some e)
    (ha : readopt ⟨k, freshRank p.val k⟩ e = .ok a) :
    normalized { p.val with store := p.val.store.set i a hs } = true := by
  rw [readopt] at ha
  split at ha
  · injection ha with ha
    subst ha
    refine normalized_after_relocation p i e _ k hs hget rfl ?_
    intro r hr
    exact absurd hr (by simp)
  · simp at ha

theorem drop_normalized (p : WfPlan) (i : Id) (e : Entity)
    (hs : (p.val.store.get i).isSome = true) (hget : p.val.store.get i = some e) :
    normalized { p.val with store := p.val.store.set i (drop e) hs } = true :=
  normalized_after_edit p i e (drop e) hs hget rfl rfl

theorem setEst_normalized (p : WfPlan) (i : Id) (e : Entity) (v : Nat)
    (hs : (p.val.store.get i).isSome = true) (hget : p.val.store.get i = some e) :
    normalized { p.val with store := p.val.store.set i (setEstE v e) hs } = true :=
  normalized_after_edit p i e (setEstE v e) hs hget rfl rfl

/-- The six conjuncts of `itemsWf` that are **not** rank distinctness.  A
command really can break any of them — a move into a day file outside
`# Pinned` breaks `sectionsWf`, a move into `month/` can break `shapesWf` — so
they stay hypotheses.  `Normalized` is the one that no longer has to be. -/
def itemsWfButRanks (p : PlanCore) : Bool :=
  parentsTotal p && parentsAcyclic p && afterTotal p && afterAcyclic p &&
    sectionsWf p && shapesWf p

theorem itemsWf_of_normalized (p : PlanCore) (h1 : normalized p = true)
    (h2 : itemsWfButRanks p = true) : itemsWf p = true := by
  simp only [itemsWfButRanks, Bool.and_eq_true] at h2
  exact itemsWf_of_parts h1 h2.1.1.1.1.1 h2.1.1.1.1.2 h2.1.1.1.2 h2.1.1.2 h2.1.2 h2.2

/-- **`cmdMove_succeeds` at the boundary, with the rank hypothesis gone.**
Cmd.lean's version needs the caller to supply `itemsWf` of the post-state,
because `rank` there is a `Nat` the caller chose.  `applyCmd` does not choose:
it passes `freshRank`, and `move_at_freshRank_normalized` discharges the
`Normalized` conjunct outright.  What is left in `hrest` is the six conjuncts a
move can genuinely violate. -/
theorem applyCmd_move_succeeds (p : WfPlan) (i : Id) (e : Entity) (n : Nat) (d : Dest p.val)
    (hn : resolveDest p.val n = .ok d) (hget : p.val.store.get i = some e)
    (hfree : ∀ r, e.val.archiveSite = some r →
      horizonPrecedes (docRegion p.val r.doc) (docRegion p.val d.ix) = true)
    (hrest : ∀ a : Entity, a.val = { e.val with live := d.site (freshRank p.val d.ix) } →
      ∀ hs : (p.val.store.get i).isSome = true,
      itemsWfButRanks { p.val with store := p.val.store.set i a hs } = true) :
    ∃ q : WfPlan, applyCmd (.move i n) p = .ok q ∧
      ∃ e', q.val.store.get i = some e' ∧ e'.val.live = d.site (freshRank p.val d.ix) := by
  have hmove := cmdMove_succeeds p i e d (freshRank p.val d.ix) hget hfree ?_
  · obtain ⟨q, hq, he'⟩ := hmove
    refine ⟨q, ?_, he'⟩
    simp only [applyCmd, hn]
    exact hq
  · intro a hva hs
    exact itemsWf_of_normalized _
      (move_at_freshRank_normalized p i e a d.ix hs hget hva) (hrest a hva hs)

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
def runPlan (plan : WfPlan) (cmds : List ReqCmd) : Except JVal JVal := do
  let plan' ←
    match applyAll cmds plan with
    | .ok q => pure q
    | .error k => throw (jone "err" (jone "kernel" (.str (kerrName k).toList)))
  let outDocs := plan'.val.docs.zipIdx.map (fun p =>
    JVal.obj
      ([("path".toList, .str p.1.path),
        ("lines".toList, .arr ((renderDocAt plan'.val p.2 p.1).map JVal.str))]
        ++ regionJson p.1.region))
  return jone "ok" (jone "docs" (.arr outDocs))

def run (j : JVal) : Except JVal JVal := do
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
    -- Absent `cmds` is a read with no commands; a `cmds` that is present but
    -- not an array is refused (it used to be swallowed as no commands, §5.7).
    match jget j "cmds" with
    | .ok none => pure []
    | .ok (some (.arr a)) => pure a
    | .ok (some _) => throw (jsonErr "array expected")
    | .error e => throw (jsonErr e)
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
    | .error e => throw (jone "err" (lerrJson e))
  -- build the plan and run the request.  `loadPlan` is the whole loader as one
  -- function, which is what makes `the_kernel_reads_back_what_it_writes` a
  -- theorem about the code the FFI runs rather than about a copy of it.
  match loadPlan docs with
  | .error e   => throw e
  | .ok plan   => runPlan plan cmds


/-! ### The round trip is not vacuous

A theorem about plans nobody can build is the defect class this kernel exists to
remove, so the witness is here and not only in the Rust suite: a concrete
request — a heading and an item line in a week file, a heading in a month file —
that `loadPlan` accepts, and the round trip for its first document written out in
bytes. -/

def sampleWeekDoc : ReqDoc :=
  ⟨"week/2026-W37.md", some ⟨week, 35⟩,
    ["# Tasks".toList, "- [ ] 5 6b Finish the report ^m1".toList]⟩

def sampleRequest : List ReqDoc :=
  [sampleWeekDoc, ⟨"month/2026-09.md", some ⟨month, 8⟩, ["# Outcomes".toList]⟩]

def loadsOk (docs : List ReqDoc) : Bool :=
  match loadPlan docs with
  | .ok _    => true
  | .error _ => false

/-- The hypothesis of `the_kernel_reads_back_what_it_writes` is satisfiable, by
decision. -/
theorem the_round_trip_is_not_vacuous : loadsOk sampleRequest = true := by decide

/-- And its conclusion at that request is a statement about bytes. -/
theorem the_round_trip_fires (p : WfPlan) (h : loadPlan sampleRequest = .ok p) :
    renderDocAt p.val 0 (mkDoc sampleWeekDoc)
      = ["# Tasks".toList, "- [ ] 5 6b Finish the report ^m1".toList] :=
  (the_kernel_reads_back_what_it_writes sampleRequest p h 0 sampleWeekDoc rfl).2

/-! ### §4.3's own demotion pair, loaded and rendered back

The two documents above have one line between them.  These two are the pair the
orientation rule is about, taken **verbatim** from §4.3 and from every
`plan-basic`-shaped tree in the corpus: the record live in the week, the archive
copy under `month/…# Demoted`, and — the half that is not about orientation at
all — two lines of one id whose bytes are different, because §6.3's close puts
`est:` = remaining and a `demoted:` stamp on the copy and a smaller leading
estimate came with it.

Both refusals this branch removes are refutable here by `decide`, so the kernel
rechecks them on every build: the loader accepts the pair, and each document
comes back byte for byte. -/

def specWeekDoc : ReqDoc :=
  ⟨"week/2026-W37.md", some ⟨week, 35⟩,
    ["# Milestones".toList,
     "- [ ] 4 6b Rollback path passes tests   @O2 ^m2".toList]⟩

def specMonthDoc : ReqDoc :=
  ⟨"month/2026-09.md", some ⟨month, 8⟩,
    ["# Demoted".toList,
     "- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2".toList]⟩

def specDemotionRequest : List ReqDoc := [specWeekDoc, specMonthDoc]

/-- The single entity the loader builds from that request, if it builds one. -/
def specPairEntity : Option Entity :=
  match buildEntities (placementsOf 0 specDemotionRequest) with
  | .ok [(_, e)] => some e
  | _            => none

set_option maxRecDepth 40000 in
/-- **The two lines become one entity, and it has a tombstone.**  Not two
entities, not one line dropped: the pair is read as the demotion it is. -/
theorem the_spec_pair_is_one_entity_with_a_tombstone :
    specPairEntity.map (fun e => e.val.archive.isSome) = some true := by decide

set_option maxRecDepth 40000 in
/-- **And this is the orientation decision itself, decided.**  Document 0 is
`week/2026-W37.md` and document 1 is `month/2026-09.md`: the **record** is the
week line and the **tombstone** is the month line, which is the answer the box
gives and the exact opposite of the one horizon order gives — the week is the
earlier horizon.  The old rule made the week line the tombstone, read `[ ]`
there, and returned `notADemotion`.

Nothing else in this package pins the choice this directly, so it is `decide`d
and the kernel rechecks it on every build. -/
theorem the_spec_pair_puts_the_tombstone_in_the_month :
    specPairEntity.map (fun e => (e.val.live.doc, e.val.archiveSite.map Site.doc))
      = some (0, some 1) := by decide

set_option maxRecDepth 40000 in
/-- **The pair loads.**  Under the old orientation the tombstone was the line in
the earlier horizon — the week — which reads `[ ]`, so this request was
`notADemotion`; under the old entity the two lines' bytes differ, so it was
`splitLine` first.  Both are gone and the acceptance is decided here. -/
theorem the_spec_demotion_pair_loads : loadsOk specDemotionRequest = true := by decide

/-- **And both of its documents come back byte for byte** — including the
month copy, whose `est:3b demoted:W37` no rendering off the week line could have
produced. -/
theorem the_spec_demotion_pair_round_trips (p : WfPlan)
    (h : loadPlan specDemotionRequest = .ok p) :
    renderDocAt p.val 0 (mkDoc specWeekDoc)
        = ["# Milestones".toList,
           "- [ ] 4 6b Rollback path passes tests   @O2 ^m2".toList] ∧
      renderDocAt p.val 1 (mkDoc specMonthDoc)
        = ["# Demoted".toList,
           "- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2".toList] :=
  ⟨(the_kernel_reads_back_what_it_writes specDemotionRequest p h 0 specWeekDoc rfl).2,
   (the_kernel_reads_back_what_it_writes specDemotionRequest p h 1 specMonthDoc rfl).2⟩

/-! ### The loader's `planWf` conjuncts, discharged (README gap 16)

`sitesInRange` and `demotionsOriented` are re-checked by `mapAt` on every
post-state, and `loadPlan` refuses a request before they could fail — but
between `loadCore` and the first command they sit between the loader and a
proof.  The converse direction was already cashed for one of the three
(`loadCore_docsWf`, and the pair-fidelity section's
`the_kernel_can_read_the_pairs_it_writes` for orientation); these are the two
that were `P*`.  `normalized` remains: it needs the `splitDoc` rank
distinctness chain, not a new idea, and is named in the README as the third
of gap 16.

The shape both proofs share is the one `buildEntity_renders` started:
`buildEntities_spec` turns the accepted list into a per-id
`buildEntity i (filter) = .ok e`, the `match` on the filter list discharges
`nil` and `3+` by noConfusion, and the two surviving arms read the entity's
places off `loneEntity` / `paired_placement_renders_back` — so nothing here
reasons about parsing at all, only about indices and orientation. -/

/-- Sites the walk builds are indices into the list it walked. -/
theorem placement_doc_lt {docs : List ReqDoc} {q : Placement}
    (hq : q ∈ placementsOf 0 docs) : q.doc < docs.length := by
  obtain ⟨j, d, hd, hqj⟩ := (mem_placementsOf q 0 docs).1 hq
  obtain ⟨it, _, hqe⟩ := mem_placementsOfDoc.1 hqj
  subst hqe
  obtain ⟨hjlt, _⟩ := List.getElem?_eq_some_iff.1 hd
  simpa using hjlt

/-- On a loaded plan, `docRegion` reads back the region the placement declared. -/
theorem docRegion_loadCore_placement (docs : List ReqDoc) (items : List (Id × Entity))
    {q : Placement} (hq : q ∈ placementsOf 0 docs) :
    docRegion (loadCore docs items) q.doc = q.region := by
  obtain ⟨j, d, hd, hqj⟩ := (mem_placementsOf q 0 docs).1 hq
  obtain ⟨it, _, hqe⟩ := mem_placementsOfDoc.1 hqj
  rw [hqe, Nat.zero_add]
  suffices h : (docs.map mkDoc)[j]? = some (mkDoc d) by
    show (match (docs.map mkDoc)[j]? with
      | none => none
      | some dd => dd.region) = d.reg
    rw [h]
    rfl
  rw [List.getElem?_map, hd]
  rfl

/-- A site naming an existing document is in range on the loaded plan. -/
theorem siteInRange_loadCore (docs : List ReqDoc) (items : List (Id × Entity))
    (s : Site) (h : s.doc < docs.length) :
    siteInRange (loadCore docs items) s = true := by
  unfold siteInRange
  exact decide_eq_true (by simpa [loadCore, List.length_map] using h)

/-- Both placements an orienter chose come from the pair it was given. -/
theorem placement_bounds_pair {ps : List Placement} {a b arch live : Placement}
    (ha : a ∈ ps) (hb : b ∈ ps)
    (hor : (arch = a ∧ live = b) ∨ (arch = b ∧ live = a)) :
    arch ∈ ps ∧ live ∈ ps := by
  obtain ⟨he1, he2⟩ | ⟨he1, he2⟩ := hor
  · rw [he1, he2]; exact ⟨ha, hb⟩
  · rw [he1, he2]; exact ⟨hb, ha⟩

/-- An entity `buildEntity` accepts has both of its sites in range on the
loaded plan.  The lone arm reads `live` off `loneEntity` and takes the empty
archive branch; the pair arm reads `live` and the tombstone's site off
`paired_placement_renders_back`, whose `orientPair` witness says the two are
the two placements it was given. -/
theorem entityInRange_loadEntity {docs : List ReqDoc} {items : List (Id × Entity)}
    {qs : List Placement} {i : Id} {e : Entity}
    (hsub : ∀ q ∈ qs, q ∈ placementsOf 0 docs)
    (h : buildEntity i qs = .ok e) :
    entityInRange (loadCore docs items) e = true := by
  match qs with
  | [] => simp [buildEntity] at h
  | [q] =>
      have h' : e = loneEntity q := by
        have this : Except.ok (loneEntity q) = (.ok e : Except LErr Entity) := h
        injection this with this
        exact this.symm
      rw [h']
      show (siteInRange (loadCore docs items) ⟨q.doc, q.rank⟩
          && match (none : Option Site) with
            | none => true
            | some r => siteInRange (loadCore docs items) r) = true
      rw [Bool.and_eq_true]
      exact ⟨siteInRange_loadCore docs items ⟨q.doc, q.rank⟩
               (placement_doc_lt (hsub q (by simp))), rfl⟩
  | [a, b] =>
      have h' : pairedEntity i a b = .ok e := h
      obtain ⟨arch, live, hor, _hcond, hllive, harch, _hline, _hag, hglive, _hgarch⟩ :=
        paired_placement_renders_back i a b e h'
      obtain ⟨har, hal⟩ := placement_bounds_pair (hsub a (by simp)) (hsub b (by simp))
        (orientPair_cases hor).1
      show (siteInRange (loadCore docs items) e.val.live
          && match e.val.archiveSite with
            | none => true
            | some r => siteInRange (loadCore docs items) r) = true
      rw [hllive, Core.archiveSite_some harch]
      rw [Bool.and_eq_true]
      exact ⟨siteInRange_loadCore docs items ⟨live.doc, live.rank⟩ (placement_doc_lt hal),
             siteInRange_loadCore docs items ⟨arch.doc, arch.rank⟩ (placement_doc_lt har)⟩

/-- An entity `buildEntity` accepts is an oriented demotion on the loaded
plan: the lone has no archive record, and in a pair the box guard's fact is
`orientPair`'s third conjunct read through `glyphAt_live`, with both regions
read back at the placements' own declared values.  This is the loader half of
gap 16's `demotionsOriented`; the command half is
`the_kernel_can_read_the_pairs_it_writes`. -/
theorem demotionOriented_loadEntity {docs : List ReqDoc} {items : List (Id × Entity)}
    {qs : List Placement} {i : Id} {e : Entity}
    (hsub : ∀ q ∈ qs, q ∈ placementsOf 0 docs)
    (h : buildEntity i qs = .ok e) :
    demotionOriented (loadCore docs items) e = true := by
  match qs with
  | [] => simp [buildEntity] at h
  | [q] =>
      have h' : e = loneEntity q := by
        have this : Except.ok (loneEntity q) = (.ok e : Except LErr Entity) := h
        injection this with this
        exact this.symm
      rw [h']
      show demotionOriented (loadCore docs items) (loneEntity q) = true
      rfl
  | [a, b] =>
      have h' : pairedEntity i a b = .ok e := h
      obtain ⟨arch, live, hor, hcond, hllive, harch, _hline, _hag, hglive, _hgarch⟩ :=
        paired_placement_renders_back i a b e h'
      obtain ⟨har, hal⟩ := placement_bounds_pair (hsub a (by simp)) (hsub b (by simp))
        (orientPair_cases hor).1
      have hgoal : demotionOriented (loadCore docs items) e =
          (if glyphOfStatus e.val.status = Glyph.demoted then
              horizonPrecedes (docRegion (loadCore docs items) arch.doc)
                (docRegion (loadCore docs items) live.doc)
            else true) := by
        unfold demotionOriented
        rw [harch, hllive]
      rw [hgoal]
      by_cases hd : glyphOfStatus e.val.status = Glyph.demoted
      · have h2 : glyphAt e.val e.val.live = Glyph.demoted := by
          have hl := glyphAt_live e.val e.property
          rw [hl]
          exact hd
        have : live.glyph = Glyph.demoted := by rw [← hglive]; exact h2
        rw [if_pos hd, docRegion_loadCore_placement docs items har,
          docRegion_loadCore_placement docs items hal]
        exact hcond this
      · rw [if_neg hd]

/-- **The loader builds sites in range** (stage 3, README gap 16).  Every site
in every entity the loader builds names a document the request actually
carried — `siteOutOfRange`, the only `err` the loader itself can emit, is
unreachable by proof, not by a check.  The check still runs (`loadPlan` calls
`sitesInRange` before asking `planWf`); this theorem says what that check was
always bound to answer. -/
theorem the_loader_builds_sites_in_range (docs : List ReqDoc) (items : List (Id × Entity))
    (h : buildEntities (placementsOf 0 docs) = .ok items) :
    sitesInRange (loadCore docs items) = true := by
  obtain hall := (buildEntities_spec (placementsOf 0 docs) items h).2
  show (loadStore items).dom.all
    (fun i => match (loadStore items).get i with
      | none => true
      | some e => entityInRange (loadCore docs items) e) = true
  rw [List.all_eq_true]
  intro i hi
  cases g : (loadStore items).get i with
  | none => rfl
  | some e =>
      exact entityInRange_loadEntity (fun q hq => (List.mem_filter.1 hq).1)
        (hall (i, e) (loadStore_get_some items i e g))

/-- **The loader builds oriented demotions** (stage 3, README gap 16, the
third conjunct).  Every entity the loader builds satisfies
`demotionsOriented` at the loaded plan's regions — the orientation the box
decided and `orientPair` fixed is the orientation `planWf` will re-check.
With `the_kernel_can_read_the_pairs_it_writes` this is both directions
between what the loader reads and what the invariant demands. -/
theorem the_loader_builds_oriented_demotions (docs : List ReqDoc) (items : List (Id × Entity))
    (h : buildEntities (placementsOf 0 docs) = .ok items) :
    demotionsOriented (loadCore docs items) = true := by
  obtain hall := (buildEntities_spec (placementsOf 0 docs) items h).2
  show (loadStore items).dom.all
    (fun i => match (loadStore items).get i with
      | none => true
      | some e => demotionOriented (loadCore docs items) e) = true
  rw [List.all_eq_true]
  intro i hi
  cases g : (loadStore items).get i with
  | none => rfl
  | some e =>
      exact demotionOriented_loadEntity (fun q hq => (List.mem_filter.1 hq).1)
        (hall (i, e) (loadStore_get_some items i e g))

/-- The two (or one) lines an entity renders are distinct.  They can only
collide if the archive site **is** the live site, and `wf` forbids exactly
that (`archive_elsewhere`). -/
theorem render_nodup (i : Id) (e : Entity) : (render i e).Nodup := by
  unfold render renderCore
  cases h : e.val.archive with
  | none => simp
  | some t =>
      refine List.nodup_cons.2 ⟨?_, by simp⟩
      intro hx
      simp at hx
      obtain ⟨hsite, _⟩ := hx
      exact absurd (congrArg Site.doc hsite)
        (Ne.symm (archive_elsewhere e t.site (Core.archiveSite_some h)))

/-- Reading distinct ids out of one store yields distinct lines: every line
carries its id's bytes in its own rendering, so a collision would name one id
twice in the domain. -/
theorem flatMap_nodup_store (p : PlanCore) :
    ∀ (ls : List Id), ls.Nodup →
      (ls.flatMap (fun i =>
        match p.store.get i with | none => [] | some e => render i e)).Nodup := by
  intro ls
  induction ls with
  | nil => intro _; simp
  | cons x t ih =>
      intro hnd
      obtain ⟨hx, ht⟩ := List.nodup_cons.1 hnd
      refine List.nodup_append.2 ⟨?_, ih ht, ?_⟩
      · match g : p.store.get x with
        | none => simp [g]
        | some e => simpa [g] using render_nodup x e
      · intro a ha b hb hab
        match g : p.store.get x with
        | none => simp [g] at ha
        | some e =>
            have hai : a.id = x := render_all_same_id x e a (by simpa [g] using ha)
            obtain ⟨j, hj, hb'⟩ := List.mem_flatMap.1 hb
            match g' : p.store.get j with
            | none => simp [g'] at hb'
            | some e' =>
                have hbi : b.id = j := render_all_same_id j e' b (by simpa [g'] using hb')
                have hxj : x = j := calc x = a.id := hai.symm
                  _ = b.id := congrArg Line.id hab
                  _ = j := hbi
                exact hx (by rw [hxj]; exact hj)

/-- **A well-formed store renders distinct lines.**  `p.lines` walks the domain
and renders; both sides of the fold keep the lines apart — distinct ids
(`domNodup`) and `render_nodup` within one entity. -/
theorem store_lines_nodup (p : PlanCore) (hn : p.store.dom.Nodup) : p.lines.Nodup :=
  flatMap_nodup_store p _ hn

/-- The domain after an insert, stated as data: the new id goes in front, or
nothing changes. -/
theorem Store.insert_dom (s : Store) (i : Id) (e : Entity) :
    (s.insert i e).dom = if i ∈ s.dom then s.dom else i :: s.dom := by
  unfold Store.insert
  split <;> rfl

/-- Folding inserts over **any** list keeps a `Nodup` domain nodup: the member
case changes nothing; the absent case conses a fresh head.  No freshness
hypothesis is needed because a re-insert collapses instead of duplicating. -/
theorem foldl_insert_dom_nodup : ∀ (items : List (Id × Entity)) (s : Store),
    s.dom.Nodup → ((items.foldl (fun s p => s.insert p.1 p.2) s)).dom.Nodup := by
  intro items
  induction items with
  | nil => intro s hs; exact hs
  | cons x t ih =>
      intro s hs
      simp only [List.foldl_cons]
      refine ih (s.insert x.1 x.2) ?_
      by_cases hm : x.1 ∈ s.dom
      · rw [Store.insert_dom, if_pos hm]; exact hs
      · rw [Store.insert_dom, if_neg hm, List.nodup_cons]
        exact ⟨fun h => absurd h hm, hs⟩

/-- Tag every rank of a distinct list with one fixed document index and the
pairs are distinct. -/
theorem slots_nodup_of_nodup (k : Nat) :
    ∀ (l : List (Nat × (Id × Glyph × RawItem))),
    (l.map Prod.fst).Nodup → (l.map (fun p => (k, p.1))).Nodup := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro hn
      obtain ⟨hnm, hnt⟩ := List.nodup_cons.1 hn
      rw [List.map_cons]
      refine List.nodup_cons.2 ⟨?_, ?_⟩
      · intro h
        obtain ⟨y, hy, heq⟩ := List.mem_map.1 h
        exact hnm (List.mem_map.2 ⟨y, hy, congrArg Prod.snd heq⟩)
      · exact ih hnt

/-- **No two placements of a request occupy the same slot.**  `(doc, rank)`
pairs of `placementsOf k docs` are distinct: within one file by
`splitDoc_items_nodup`, across files because each file's placements carry the
index of their own file.  This is the structural fact behind `normalized`: no
command had to be run for it — it holds of the request itself. -/
theorem placements_slot_nodup :
    ∀ (docs : List ReqDoc) (k : Nat),
    ((placementsOf k docs).map (fun q => (q.doc, q.rank))).Nodup := by
  intro docs
  induction docs with
  | nil => intro k; simp [placementsOf]
  | cons d rest ih =>
      intro k
      show ((placementsOfDoc k d.reg (splitDoc 0 d.lines) ++
          placementsOf (k + 1) rest).map (fun q => (q.doc, q.rank))).Nodup
      rw [List.map_append, List.nodup_append]
      refine ⟨?_, ih (k + 1), ?_⟩
      · have hmap : (placementsOfDoc k d.reg (splitDoc 0 d.lines)).map
            (fun q => (q.doc, q.rank)) =
          ((splitDoc 0 d.lines).items.map fun it => (k, it.1)) := by
          simp only [placementsOfDoc]
          rw [List.map_map]
          rfl
        rw [hmap]
        exact slots_nodup_of_nodup k _ (splitDoc_items_nodup 0 d.lines)
      · intro a ha b hb hab
        obtain ⟨qa, hqam, hra⟩ := List.mem_map.1 ha
        obtain ⟨qb, hqbm, hrb⟩ := List.mem_map.1 hb
        obtain ⟨it, hit, hqa⟩ := mem_placementsOfDoc.1 hqam
        obtain ⟨j, d2, hd2, hq0⟩ := (mem_placementsOf qb (k + 1) rest).1 hqbm
        obtain ⟨it2, hit2, hqb'⟩ := mem_placementsOfDoc.1 hq0
        have hp : (qa.doc, qa.rank) = (qb.doc, qb.rank) :=
          hra.trans (hab.trans hrb.symm)
        have h1 : qa.doc = qb.doc := congrArg Prod.fst hp
        have hqadoc : qa.doc = (k : Nat) := by rw [hqa]
        have hqbdoc : qb.doc = (k + 1 + j : Nat) := by rw [hqb']
        have h2 : (k : Nat) = k + 1 + j :=
          calc (k : Nat) = qa.doc := hqadoc.symm
            _ = qb.doc := h1
            _ = k + 1 + j := hqbdoc
        exact absurd h2 (by omega)

/-- If every line of a list names a placement slot, and distinct lines name
placements whose slots are distinct, then the lines of any one document have
distinct ranks: an equal rank in one document would make two lines equal. -/
theorem ranksIn_nodup_lines {docs : List ReqDoc}
    (hpl : ((placementsOf 0 docs).map (fun q => (q.doc, q.rank))).Nodup) :
    ∀ (ls : List Line), (∀ l ∈ ls, ∃ q ∈ placementsOf 0 docs, l = placementLine q) →
    ls.Nodup → ∀ k, (ranksIn k ls).Nodup := by
  intro ls
  induction ls with
  | nil => intro _ _ _; simp [ranksIn]
  | cons x t ih =>
      intro hH hN k
      have hHt : ∀ l ∈ t, ∃ q ∈ placementsOf 0 docs, l = placementLine q :=
        fun l hl => hH l (List.mem_cons_of_mem x hl)
      obtain ⟨hn1, hn2⟩ := List.nodup_cons.1 hN
      by_cases hd : (x.site.doc == k) = true
      · rw [ranksIn, List.filter_cons, if_pos hd, List.map_cons, List.nodup_cons]
        refine ⟨fun hr => ?_, ih hHt hn2 k⟩
        have hxd : x.site.doc = k := by simpa using hd
        obtain ⟨m, hm, hmd, hmr⟩ := mem_ranksIn.1 hr
        obtain ⟨ql, hql, hlq⟩ := hH x (by simp)
        obtain ⟨qm, hqm, hmq⟩ := hH m (List.mem_cons.2 (Or.inr hm))
        have e1 : x.site = ⟨ql.doc, ql.rank⟩ := by rw [hlq]; rfl
        have e2 : m.site = ⟨qm.doc, qm.rank⟩ := by rw [hmq]; rfl
        have hdom : ql.doc = qm.doc := calc ql.doc = x.site.doc :=
            (congrArg Site.doc e1).symm
          _ = k := hxd
          _ = m.site.doc := hmd.symm
          _ = qm.doc := congrArg Site.doc e2
        have hrank : ql.rank = qm.rank := calc ql.rank = x.site.rank :=
            (congrArg Site.rank e1).symm
          _ = m.site.rank := hmr.symm
          _ = qm.rank := congrArg Site.rank e2
        have : ql = qm := nodup_map_inj hpl _ hql _ hqm (Prod.ext hdom hrank)
        subst this
        have hxm : x = m := hlq.trans hmq.symm
        rw [← hxm] at hm
        exact hn1 hm
      · rw [ranksIn, List.filter_cons, if_neg hd]
        exact ih hHt hn2 k

/-- An index below a list's length has a value there. -/
theorem getElem?_eq_some_of_lt {α : Type} : ∀ (l : List α) {i : Nat},
    i < l.length → ∃ a, l[i]? = some a := by
  intro l
  induction l with
  | nil => intro i h; exact absurd h (Nat.not_lt_zero i)
  | cons x t ih =>
      intro i h
      match i with
      | 0 => exact ⟨x, rfl⟩
      | n + 1 => exact ih (by simpa using h)

/-- **The loader builds a normalized plan** (stage 3, README gap 16, closing
it).  `normalized` is the conjunct `rankCollision` reads; this says the
`itemCheck: rankCollision` fault is unreachable from a request that loaded at
all.  Three facts assemble it: each file's prose ranks are distinct, each
file's item ranks are distinct (`splitDoc` is a partition of the line
indices — `splitDoc_prose_nodup`, `splitDoc_items_nodup`,
`splitDoc_slots_separated`), and every stored line names a placement slot of
the request, slots of one file being pairwise distinct
(`placements_slot_nodup`, `loadCore_lines_mem`).  No command was run: this is
the shape of a request, held constant across all of them. -/
theorem the_loader_builds_a_normalized_plan (docs : List ReqDoc) (items : List (Id × Entity))
    (h : buildEntities (placementsOf 0 docs) = .ok items) :
    normalized (loadCore docs items) = true := by
  obtain ⟨hmap, hall⟩ := buildEntities_spec _ _ h
  have hnd : (items.map Prod.fst).Nodup := by rw [hmap]; exact dedupIds_nodup _
  simp only [normalized, List.all_eq_true, decide_eq_true_eq]
  intro k hk
  have hkl : k < docs.length := by simpa [loadCore] using hk
  obtain ⟨rd, hrd⟩ := getElem?_eq_some_of_lt docs hkl
  have hpr : proseRanks (loadCore docs items) k = (splitDoc 0 rd.lines).prose.map Prod.fst := by
    unfold proseRanks
    rw [show (loadCore docs items).docs = docs.map mkDoc from rfl]
    have hmk : (docs.map mkDoc)[k]? = some (mkDoc rd) := by
      rw [List.getElem?_map, hrd]; rfl
    rw [hmk]
    rfl
  rw [docRanks_eq, hpr]
  show ((splitDoc 0 rd.lines).prose.map Prod.fst ++
    ranksIn k (loadCore docs items).lines).Nodup
  refine List.nodup_append.2 ⟨?_, ?_, ?_⟩
  · exact splitDoc_prose_nodup 0 rd.lines
  · refine ranksIn_nodup_lines (placements_slot_nodup docs 0) (loadCore docs items).lines
      (fun l hl => (loadCore_lines_mem docs items h l).mp hl) ?_ k
    exact store_lines_nodup (loadCore docs items)
      (by unfold loadCore; exact foldl_insert_dom_nodup items emptyStore (by simp [emptyStore]))
  · intro rp hrp r hri hne
    obtain ⟨m, hm, hmd, hmr⟩ := mem_ranksIn.1 hri
    obtain ⟨q, hq, he⟩ := (loadCore_lines_mem docs items h m).mp hm
    obtain ⟨j, d2, hd2, hq0⟩ := (mem_placementsOf q 0 docs).1 hq
    obtain ⟨it, hit, hqe⟩ := mem_placementsOfDoc.1 hq0
    have hsite : m.site = ⟨q.doc, q.rank⟩ := by rw [he]; exact rfl
    have hqk : q.doc = k :=
      (congrArg Site.doc hsite).symm.trans hmd
    have h0 : (0 + j : Nat) = q.doc := by rw [hqe]
    have hjk : j = k := calc (j : Nat) = 0 + j := (Nat.zero_add j).symm
      _ = q.doc := h0
      _ = k := hqk
    have hd2rd : d2 = rd := by
      have he2 : some d2 = some rd := by rw [← hd2, hjk, hrd]
      exact Option.some.inj he2
    have hrpItem : rp ∈ ((splitDoc 0 rd.lines).items.map Prod.fst) := by
      refine List.mem_map.2 ⟨it, ?_, ?_⟩
      · rw [← hd2rd]; exact hit
      · have hr1 : m.site.rank = (q.rank : Nat) := congrArg Site.rank hsite
        calc (it.1 : Nat) = q.rank := (by rw [hqe] : (q.rank : Nat) = it.1).symm
          _ = m.site.rank := hr1.symm
          _ = r := hmr
          _ = rp := hne.symm
    exact splitDoc_slots_separated 0 rd.lines rp hrp hrpItem

/-! ### README gap 6: the `String`/`List Char` edge, closed

Every `ReqDoc` line crosses `String → List Char` on the way in and
`List Char → String` on the way out, twice per call.  The general statement
discharges for free: it *is* core's `String.ofList_toList` (`Init` proves the
round trip as a `@[simp]` theorem — a propositional lemma this theorem applies
by name, not a definitional unfolding).  That settles the char half of gap 6.

The JSON half was `Lean.Json.parse j.compress = .ok j`, which the toolchain's
`partial def`s make neither provable nor refutable (README "Gap 39 REPRICED").
**Closed by replacement at J5–J6, 2026-09-12**: `call` below reads with the
kernel's own `jparse` and writes with `jemit`, and
`the_response_call_emits_parses_back` (end of file) is the round trip at the
exported function.  The legacy `String.splitOn` half was restated over the
kernel's structural `Tm.splitOn` and discharged (README gap 12's block). -/
theorem the_char_edge_round_trips (s : String) : String.ofList s.toList = s :=
  @String.ofList_toList s

/-- **The response value for a request's bytes.**  Every path returns one: a
parse refusal is `bad json: ` and `jerrText`'s name for it, never a default.
`call` is this, emitted — split out so that
`the_response_call_emits_parses_back` is about the exported function's bytes. -/
def respond (input : List Char) : JVal :=
  match jparse input with
  | .error e => jsonErr s!"bad json: {jerrText e}"
  | .ok j =>
    match run j with
    | .error e => e
    | .ok r    => r

/-- Total: every path returns a `String`.  No `panic!`, no `!`, no `partial`.
No `Lean.Json` either: `jparse` in, `jemit` out (J5). -/
def call (input : String) : String := String.ofList (jemit (respond input.toList))

@[export tm_kernel_call]
def callExport (input : String) : String := call input

/-! ## §5.8 for `rank` and `add` — the owed forms, landed

The 2026-09-12 README block records three owed theorems by name: a Lean-level
rank *rejection* (the taken-rank refusal existed only as the Rust test
`rank_onto_a_taken_rank_is_refused_and_writes_nothing`), `cmdRank_succeeds`,
and `cmdAdd_succeeds`.  All three land here, at the end of the file, so every
Boundary.lean line number the ledger cites above stays true. -/

/-- **The check bites (§5.8), and it is the one the FFI observes.**  Ranking an
item onto a rank another line of its document already occupies is refused as
`badHorizon` and nothing is written.  `setRankE` itself cannot fail — `wf`
never speaks of ranks (`wf_setRank`) — so the refusal is `mapAt`'s `planWf`
re-check finding `Normalized` false on the post-state: the occupant survives
the single-entity swap (`lines_set`) and collides with the rewritten live
line.  The occupant is quantified as a member of `p.val.lines` — the lines the
plan renders to disk (§5.9).  The wire witness is the W37 fixture's `^t3` at
rank 5. -/
theorem rank_onto_a_taken_rank_is_refused (p : WfPlan) (i : Id) (e : Entity) (n : Nat)
    (m : Line) (hget : p.val.store.get i = some e) (hm : m ∈ p.val.lines)
    (hmi : m.id ≠ i) (hsite : m.site = ⟨e.val.live.doc, n⟩) :
    applyCmd (.rank i n) p = .error .badHorizon := by
  have hs : (p.val.store.get i).isSome = true := by rw [hget]; rfl
  have hwf : wf { e.val with live := ⟨e.val.live.doc, n⟩ } = true := by
    rw [wf_setRank]; exact e.property
  have hf : setRankE n e = .ok ⟨_, hwf⟩ := by
    unfold setRankE; exact lift_ok_of_wf _ hwf
  have hq : ¬ planWf { p.val with
      store := (p.val.store.set i (⟨_, hwf⟩ : Entity) hs) } = true := by
    intro hc
    obtain ⟨A, C, hp, hp', hA, hC⟩ := lines_set p.val i e (⟨_, hwf⟩ : Entity) hs hget
    have hmnotr : m ∉ render i e := fun hr => hmi (render_all_same_id i e m hr)
    have hmAC : m ∈ A ∨ m ∈ C := by
      rw [hp] at hm
      rcases List.mem_append.1 hm with h1 | h1
      · exact Or.inl h1
      · rcases List.mem_append.1 h1 with h2 | h2
        · exact absurd h2 hmnotr
        · exact Or.inr h2
    obtain ⟨l₀, hl₀, hl₀s⟩ := live_line_site_mem i (⟨_, hwf⟩ : Entity)
    have hk : e.val.live.doc < p.val.docs.length := by
      have h0 := entityInRange_of_mem p i e hget
      simp only [entityInRange, Bool.and_eq_true, siteInRange, decide_eq_true_eq] at h0
      exact h0.1
    have hnorm := (itemsWf_parts (planWf_parts hc).2.2.2.2).1
    simp only [normalized, List.all_eq_true, decide_eq_true_eq] at hnorm
    have hnd := hnorm e.val.live.doc (List.mem_range.2 hk)
    rw [docRanks_eq, hp', ranksIn_append, ranksIn_append] at hnd
    have hnr : n ∈ ranksIn e.val.live.doc (render i (⟨_, hwf⟩ : Entity)) :=
      mem_ranksIn.2 ⟨l₀, hl₀, by rw [hl₀s], by rw [hl₀s]⟩
    have h1 := List.nodup_append.1 hnd
    have h2 := List.nodup_append.1 h1.2.1
    rcases hmAC with hin | hin
    · exact h2.2.2 n (mem_ranksIn.2 ⟨m, hin, by rw [hsite], by rw [hsite]⟩) n
        (List.mem_append.2 (Or.inl hnr)) rfl
    · have h3 := List.nodup_append.1 h2.2.1
      exact h3.2.2 n hnr n (mem_ranksIn.2 ⟨m, hin, by rw [hsite], by rw [hsite]⟩) rfl
  show cmdRank i n p = .error .badHorizon
  unfold cmdRank WfPlan.mapAt
  split
  · rename_i hn'; rw [hget] at hn'; simp at hn'
  · rename_i e' hget'
    rw [hget] at hget'
    injection hget' with hget'
    subst hget'
    rw [hf]
    simp only [dif_neg hq]

/-- The `SitesFree` obligation of a rank rewrite whose target rank nothing else
holds: the live line lands on the free site, and any tombstone stays exactly
where it was — a site the old entity already occupied. -/
theorem setRank_sitesFree (p : WfPlan) (i : Id) (e a : Entity) (n : Nat)
    (hget : p.val.store.get i = some e)
    (hva : a.val = { e.val with live := ⟨e.val.live.doc, n⟩ })
    (hlines : ∀ m ∈ p.val.lines, m.site = (⟨e.val.live.doc, n⟩ : Site) → m ∈ render i e)
    (hprose : ∀ d, p.val.docs[e.val.live.doc]? = some d → ∀ q ∈ d.prose, q.1 ≠ n) :
    SitesFree p.val i e a := by
  intro l hl
  rcases render_site i a l hl with hlive | harch
  · have hsl : l.site = (⟨e.val.live.doc, n⟩ : Site) := by rw [hlive, hva]
    constructor
    · intro m hm hms
      exact hlines m hm (by rw [hms, hsl])
    · intro d hd q hq hqr
      have hldoc : l.site.doc = e.val.live.doc := by rw [hsl]
      have hlrank : l.site.rank = n := by rw [hsl]
      have hd2 : p.val.docs[e.val.live.doc]? = some d := by rw [← hldoc]; exact hd
      exact hprose d hd2 q hq (hqr.trans hlrank)
  · have harchdef : a.val.archive = e.val.archive := by rw [hva]
    cases hta : a.val.archive with
    | none => rw [Core.archiveSite_none hta] at harch; simp at harch
    | some t =>
        have hts : t.site = l.site :=
          Option.some.inj ((Core.archiveSite_some hta).symm.trans harch)
        have hte : e.val.archive = some t := by rw [← harchdef]; exact hta
        obtain ⟨m0, hm0, hm0s⟩ := archive_line_mem i e t hte
        have hm0l : m0 ∈ p.val.lines := mem_lines_of_render p.val i e m0 hget hm0
        constructor
        · intro m hm hms
          have hmm : m = m0 := site_names_one_line p m m0 hm hm0l (by rw [hms, hm0s, hts])
          rw [hmm]; exact hm0
        · intro d hd q hq
          have hd' : p.val.docs[m0.site.doc]? = some d := by rw [hm0s, hts]; exact hd
          have hne := no_prose_line_shares_a_rank p m0 hm0l d hd' q hq
          rw [hm0s, hts] at hne
          exact hne

/-- **`cmdMove_succeeds`' mirror for the rank verb — the owed success form
(§5.8's other direction).**  Every hypothesis is load-bearing and honest:
`hlines` says the target rank is free among the document's item lines — any
plan line already at `⟨doc, n⟩` is one of this item's own, which is what makes
L20a's idempotent re-rank a success rather than a refusal; `hprose` says no
heading or prose line owns the rank (`Normalized` counts both in one list);
`hrest` is the six `itemsWf` conjuncts a rank rewrite can genuinely break —
a day-file line ranked out of `# Pinned` is a legitimate `sectionsWf` refusal
(`add_outside_a_day_files_pinned_section_is_refused_by_name` shows the same
discipline biting on the wire).  `Normalized` is discharged, not assumed:
`lines_set`/`normalized_set` (Plan.lean) turn the two freshness hypotheses into
the re-check's rank conjunct.  Satisfiability: kernel.rs's
`rank_moves_a_line_within_its_own_file` (rank 10 in the W37 fixture) is a wire
witness for every hypothesis at once. -/
theorem cmdRank_succeeds (p : WfPlan) (i : Id) (e : Entity) (n : Nat)
    (hget : p.val.store.get i = some e)
    (hlines : ∀ m ∈ p.val.lines, m.site = (⟨e.val.live.doc, n⟩ : Site) → m ∈ render i e)
    (hprose : ∀ d, p.val.docs[e.val.live.doc]? = some d → ∀ q ∈ d.prose, q.1 ≠ n)
    (hrest : ∀ a : Entity, a.val = { e.val with live := ⟨e.val.live.doc, n⟩ } →
      ∀ hs : (p.val.store.get i).isSome = true,
      itemsWfButRanks { p.val with store := p.val.store.set i a hs } = true) :
    ∃ q : WfPlan, cmdRank i n p = .ok q ∧
      ∃ e', q.val.store.get i = some e' ∧ e'.val.live = ⟨e.val.live.doc, n⟩ := by
  have hwf : wf { e.val with live := ⟨e.val.live.doc, n⟩ } = true := by
    rw [wf_setRank]; exact e.property
  have hf : setRankE n e = .ok ⟨_, hwf⟩ := by
    unfold setRankE; exact lift_ok_of_wf _ hwf
  have hin : entityInRange p.val (⟨_, hwf⟩ : Entity) = true :=
    entityInRange_of_mem p i e hget
  have hdom : i ∈ p.val.store.dom := (p.val.store.domSpec i).mpr (by rw [hget]; rfl)
  have hore := List.all_eq_true.1 (planWf_parts p.property).2.2.2.1 i hdom
  rw [hget] at hore
  have hor : demotionOriented p.val (⟨_, hwf⟩ : Entity) = true := hore
  obtain ⟨q, hq, hqi, _⟩ := mapAt_ok_of_inRange p i (setRankE n) e _ hget hf hin hor
    (fun hs => itemsWf_of_normalized _
      (normalized_set p.val i e _ hs hget (itemsWf_parts p.items).1
        (setRank_sitesFree p i e _ n hget rfl hlines hprose))
      (hrest ⟨_, hwf⟩ rfl hs))
  exact ⟨q, hq, _, hqi, rfl⟩

/-- The same at the wire verb: `applyCmd (.rank i n)` **is** `cmdRank i n`, so
the success form holds of the request path under the same hypotheses. -/
theorem applyCmd_rank_succeeds (p : WfPlan) (i : Id) (e : Entity) (n : Nat)
    (hget : p.val.store.get i = some e)
    (hlines : ∀ m ∈ p.val.lines, m.site = (⟨e.val.live.doc, n⟩ : Site) → m ∈ render i e)
    (hprose : ∀ d, p.val.docs[e.val.live.doc]? = some d → ∀ q ∈ d.prose, q.1 ≠ n)
    (hrest : ∀ a : Entity, a.val = { e.val with live := ⟨e.val.live.doc, n⟩ } →
      ∀ hs : (p.val.store.get i).isSome = true,
      itemsWfButRanks { p.val with store := p.val.store.set i a hs } = true) :
    ∃ q : WfPlan, applyCmd (.rank i n) p = .ok q ∧
      ∃ e', q.val.store.get i = some e' ∧ e'.val.live = ⟨e.val.live.doc, n⟩ :=
  cmdRank_succeeds p i e n hget hlines hprose hrest

/-! ### `add` succeeds — the insert-shaped replacement lemma, then the theorem

`lines_set` covers a store whose domain does not move.  `add` extends the
domain, so it needs the insert-shaped analogue: the new plan's line list is the
new entity's lines in front of the old list, verbatim.  Everything after that
is the `freshRank` arithmetic already on file. -/

theorem lines_insertFresh (p : PlanCore) (i : Id) (e : Entity)
    (hfresh : (p.store.get i).isNone = true) :
    PlanCore.lines { p with store := p.store.insertFresh i e hfresh } =
      render i e ++ p.lines := by
  show (p.store.insertFresh i e hfresh).dom.flatMap _ = _
  rw [Store.dom_insertFresh, List.flatMap_cons]
  simp only [Store.get_insertFresh_self]
  congr 1
  show p.store.dom.flatMap _ = p.store.dom.flatMap _
  refine flatMap_congr _ _ _ (fun j hj => ?_)
  have hji : j ≠ i := by
    intro hc
    rw [hc] at hj
    have h1 := (p.store.domSpec i).mp hj
    cases hg : p.store.get i with
    | none => rw [hg] at h1; exact absurd h1 (by simp)
    | some a => rw [hg] at hfresh; exact absurd hfresh (by simp)
  rw [Store.get_insertFresh_other _ _ _ _ _ hji]

/-- **`Normalized` survives an insert whose every line sits at `freshRank`.**
The insert-shaped sibling of `normalized_of_fresh_or_old`: the new block meets
nothing — `freshRank_gt` beats the item lines, `docProseMax_ge` the prose. -/
theorem normalized_insertFresh_of_fresh (p : WfPlan) (i : Id) (e : Entity) (k : DocIx)
    (hfresh : (p.val.store.get i).isNone = true)
    (hsites : ∀ l ∈ render i e, l.site = (⟨k, freshRank p.val k⟩ : Site)) :
    normalized { p.val with store := p.val.store.insertFresh i e hfresh } = true := by
  have hl := lines_insertFresh p.val i e hfresh
  simp only [normalized, List.all_eq_true, decide_eq_true_eq]
  intro j hj
  have hold : (docRanks p.val j).Nodup := by
    have hn := (itemsWf_parts p.items).1
    simp only [normalized, List.all_eq_true, decide_eq_true_eq] at hn
    exact hn j hj
  rw [docRanks_eq, hl, ranksIn_append]
  rw [docRanks_eq] at hold
  have holdp := List.nodup_append.1 hold
  refine List.nodup_append.2 ⟨holdp.1,
    List.nodup_append.2 ⟨ranksIn_render_nodup i e j, holdp.2.1, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨l, hl', hld, hlr⟩ := mem_ranksIn.1 hx
    have hsl := hsites l hl'
    have hjk : j = k := by rw [← hld, hsl]
    have hx' : x = freshRank p.val k := by rw [← hlr, hsl]
    obtain ⟨m, hm, hmd, hmr⟩ := mem_ranksIn.1 hy
    have hlt := freshRank_gt p.val k m hm (by rw [hmd, hjk])
    omega
  · intro x hx y hy hxy
    rcases List.mem_append.1 hy with hy' | hy'
    · obtain ⟨l, hl', hld, hlr⟩ := mem_ranksIn.1 hy'
      have hsl := hsites l hl'
      have hjk : j = k := by rw [← hld, hsl]
      have hy2 : y = freshRank p.val k := by rw [← hlr, hsl]
      obtain ⟨d, hd, q, hq, hqr⟩ := mem_proseRanks hx
      have h1 : q.1 ≤ docProseMax p.val j := docProseMax_ge p.val j d hd q hq
      have h2 : docProseMax p.val k < freshRank p.val k :=
        Nat.lt_succ_of_le (Nat.le_max_left _ _)
      subst hjk
      omega
    · exact holdp.2.2 x hx y hy' hxy

/-- An `add`'s entity renders exactly one line, and it is at `freshRank`. -/
theorem add_at_freshRank_normalized (p : WfPlan) (i : Id) (d : Dest p.val)
    (title : List Char) (hfresh : (p.val.store.get i).isNone = true) :
    normalized { p.val with
      store := (p.val.store.insertFresh i (addEntity p.val d i title) hfresh) } = true := by
  refine normalized_insertFresh_of_fresh p i _ d.ix hfresh ?_
  intro l hl
  rcases render_site i _ l hl with h | h
  · rw [h]; rfl
  · rw [Core.archiveSite_none rfl] at h; simp at h

/-- The domain grew by one entity whose placements are in range, so
`sitesInRange` — a `planWf` conjunct outside `itemsWf` — is re-established. -/
theorem sitesInRange_insertFresh (p : WfPlan) (i : Id) (e : Entity)
    (hfresh : (p.val.store.get i).isNone = true)
    (hin : entityInRange p.val e = true) :
    sitesInRange { p.val with store := p.val.store.insertFresh i e hfresh } = true := by
  have hnotmem : i ∉ p.val.store.dom := by
    intro hc
    have h1 := (p.val.store.domSpec i).mp hc
    cases hg : p.val.store.get i with
    | none => rw [hg] at h1; exact absurd h1 (by simp)
    | some a => rw [hg] at hfresh; exact absurd hfresh (by simp)
  simp only [sitesInRange, Store.dom_insertFresh, List.all_cons, Bool.and_eq_true]
  constructor
  · simp only [Store.get_insertFresh_self]
    exact hin
  · simp only [List.all_eq_true]
    intro j hj
    have hji : j ≠ i := fun hc => hnotmem (hc ▸ hj)
    rw [Store.get_insertFresh_other _ _ _ _ _ hji]
    exact List.all_eq_true.1 (planWf_parts p.property).2.1 j hj

/-- ...and so is `demotionsOriented`, the other one. -/
theorem demotionsOriented_insertFresh (p : WfPlan) (i : Id) (e : Entity)
    (hfresh : (p.val.store.get i).isNone = true)
    (hor : demotionOriented p.val e = true) :
    demotionsOriented { p.val with store := p.val.store.insertFresh i e hfresh } = true := by
  have hnotmem : i ∉ p.val.store.dom := by
    intro hc
    have h1 := (p.val.store.domSpec i).mp hc
    cases hg : p.val.store.get i with
    | none => rw [hg] at h1; exact absurd h1 (by simp)
    | some a => rw [hg] at hfresh; exact absurd hfresh (by simp)
  simp only [demotionsOriented, Store.dom_insertFresh, List.all_cons, Bool.and_eq_true]
  constructor
  · simp only [Store.get_insertFresh_self]
    exact hor
  · simp only [List.all_eq_true]
    intro j hj
    have hji : j ≠ i := fun hc => hnotmem (hc ▸ hj)
    rw [Store.get_insertFresh_other _ _ _ _ _ hji]
    exact List.all_eq_true.1 (planWf_parts p.property).2.2.2.1 j hj

/-- **`cmdAdd_succeeds` — the owed success form for `add` (§5.8), completing
its three conditional laws.**  `insertFresh`'s `planWf` re-check is discharged
conjunct by conjunct: `docsWf` and `pathsDistinct` read only `docs`, which the
insert does not touch; the new entity's placement is in range because a `Dest`
carries the proof; a fresh `add` has no tombstone to orient; and `Normalized`
is the `freshRank` argument (`add_at_freshRank_normalized`).  What stays a
hypothesis is `itemsWfButRanks` of the post-state — the six conjuncts an `add`
can genuinely violate, and does: a day-file `add` outside `# Pinned` is
refused through exactly this check
(`add_outside_a_day_files_pinned_section_is_refused_by_name`, kernel.rs), so
discharging it outright would prove a false theorem.  Satisfiability of every
hypothesis at once: `add_inserts_a_fresh_id_into_the_requested_file` and
`two_adds_in_one_request_get_two_ids_and_two_ranks` (kernel.rs) are wire
witnesses.  The conclusion names what reaches the disk: the id L21 generated,
stored, at `freshRank` in the requested document (§5.9). -/
theorem cmdAdd_succeeds (p : WfPlan) (seed n : Nat) (title : List Char) (d : Dest p.val)
    (hn : resolveDest p.val n = .ok d)
    (hrest : ∀ hfresh : (p.val.store.get (freshId seed p.val.store.dom)).isNone = true,
      itemsWfButRanks { p.val with
        store := (p.val.store.insertFresh (freshId seed p.val.store.dom)
          (addEntity p.val d (freshId seed p.val.store.dom) title) hfresh) } = true) :
    ∃ q : WfPlan, applyCmd (.add seed n title) p = .ok q ∧
      ∃ e, q.val.store.get (freshId seed p.val.store.dom) = some e ∧
        e.val.live = ⟨n, freshRank p.val n⟩ := by
  have hfresh : (p.val.store.get (freshId seed p.val.store.dom)).isNone = true :=
    store_get_isNone_of_not_mem (add_assigns_a_fresh_id seed _)
  have hinr : entityInRange p.val
      (addEntity p.val d (freshId seed p.val.store.dom) title) = true := by
    simp only [entityInRange, Bool.and_eq_true]
    refine ⟨?_, rfl⟩
    simp only [siteInRange, addEntity, addCore, Dest.site]
    exact decide_eq_true d.ok
  have hpw : planWf { p.val with
      store := (p.val.store.insertFresh (freshId seed p.val.store.dom)
        (addEntity p.val d (freshId seed p.val.store.dom) title) hfresh) } = true :=
    planWf_of_parts (planWf_parts p.property).1
      (sitesInRange_insertFresh p _ _ hfresh hinr)
      (planWf_parts p.property).2.2.1
      (demotionsOriented_insertFresh p _ _ hfresh rfl)
      (itemsWf_of_normalized _
        (add_at_freshRank_normalized p (freshId seed p.val.store.dom) d title hfresh)
        (hrest hfresh))
  refine ⟨⟨_, hpw⟩, ?_, ?_⟩
  · simp only [applyCmd, hn]
    unfold WfPlan.insertFresh
    split
    · exact congrArg Except.ok (Subtype.ext rfl)
    · rename_i hq2
      exact absurd hpw hq2
  · refine ⟨addEntity p.val d (freshId seed p.val.store.dom) title, ?_, ?_⟩
    · exact Store.get_insertFresh_self p.val.store _ _ hfresh
    · show (⟨d.ix, freshRank p.val d.ix⟩ : Site) = ⟨n, freshRank p.val n⟩
      rw [resolveDest_ix hn]

/-! ### L22, refuted: no command inverts a move

`move_out_and_back_is_not_the_inverse` above refuted one composite — move out,
move back.  The plan's stronger claim (L22, "undo ∘ cmd = id on the nose") is
that *some* function of the request could serve as `tm undo`; the refutation
below is general over that function.  The witness is the corrected 2026-09-12
analysis, compiled: two items in the week file, so `^m2`'s line survives above
the rank `^m1` vacates.  After `move ^m1 1`, whatever single command `inv`
answers with fails on one observable per shape — a command at another id
leaves `^m1`'s moved site standing, because `Store.get` is a function;
`drop`/`est` keep the moved site while the original plan has it elsewhere;
`rank` keeps the document; `readopt` refuses a live record outright; `demote`
leaves a tombstone the original does not carry; `add` grows the store's
domain; and a `move` back lands on `freshRank`, which `freshRank_gt` pushes
strictly past `^m2`'s surviving rank.  Consequence, in the plan's own words:
**`tm undo` must replay the log, never apply an inverse command.** -/

def undoWitnessRequest : List ReqDoc :=
  [⟨"week/2026-W37.md", some ⟨week, 35⟩,
      ["# Tasks".toList, "- [ ] 5 6b Finish the report ^m1".toList,
       "- [ ] 5 6b Write the tests ^m2".toList]⟩,
   ⟨"month/2026-09.md", some ⟨month, 8⟩, ["# Outcomes".toList]⟩]

theorem the_undo_witness_loads : loadsOk undoWitnessRequest = true := by decide

/-- The loaded witness plan.  Total by `the_undo_witness_loads`: the error
branch is refuted, not defaulted. -/
def undoWitnessPlan : WfPlan :=
  match h : loadPlan undoWitnessRequest with
  | .ok p => p
  | .error _ => absurd the_undo_witness_loads (by simp [loadsOk, h])

/-- **L22 (R\*), refuted at the witness.**  There is no `inv : ReqCmd → ReqCmd`
with `applyCmd (inv (.move i n)) ∘ applyCmd (.move i n) = id` wherever the move
succeeded — the exact negation of the stated law, quantifier for quantifier. -/
theorem move_has_no_inverse_command :
    ¬ ∃ inv : ReqCmd → ReqCmd, ∀ (p q : WfPlan) (i : Id) (n : Nat),
      applyCmd (.move i n) p = .ok q → applyCmd (inv (.move i n)) q = .ok p := by
  rintro ⟨inv, hinv⟩
  -- the witness move fires: `^m1` leaves `⟨0, 1⟩` for `⟨1, freshRank _ 1⟩`
  have hb : (match applyCmd (.move "m1".toList 1) undoWitnessPlan with
             | .ok _ => true | .error _ => false) = true := by decide
  cases hmv : applyCmd (.move "m1".toList 1) undoWitnessPlan with
  | error k => rw [hmv] at hb; simp at hb
  | ok q =>
    have hcon := hinv undoWitnessPlan q "m1".toList 1 hmv
    -- decompose the move: one entity replaced, everything else untouched
    have hlen : 1 < undoWitnessPlan.val.docs.length := by decide
    have hrd : resolveDest undoWitnessPlan.val 1 = .ok ⟨1, hlen⟩ := by
      unfold resolveDest; exact dif_pos hlen
    simp only [applyCmd, hrd, cmdMove, Dest.site] at hmv
    obtain ⟨e, e1, hs, hgetE, hfE, hshape⟩ :=
      mapAt_ok_shape undoWitnessPlan q "m1".toList _ hmv
    unfold moveTo at hfE
    have he1v := lift_roundtrips _ _ hfE
    -- the pre-move entity, in concrete bytes
    have hml : e.val.live = ⟨0, 1⟩ := by
      have h := (by decide : (undoWitnessPlan.val.store.get "m1".toList).map
        (fun x : Entity => x.val.live) = some ⟨0, 1⟩)
      rw [hgetE] at h; simpa using h
    have hst : e.val.status = Status.live .free := by
      have h := (by decide : (undoWitnessPlan.val.store.get "m1".toList).map
        (fun x : Entity => x.val.status) = some (Status.live .free))
      rw [hgetE] at h; simpa using h
    have har : e.val.archive = none := by
      have h := (by decide : (undoWitnessPlan.val.store.get "m1".toList).map
        (fun x : Entity => x.val.archive) = some none)
      rw [hgetE] at h; simpa using h
    -- the post-move entity and store
    have he1live : e1.val.live = ⟨1, freshRank undoWitnessPlan.val 1⟩ := by rw [he1v]
    have he1st : e1.val.status = Status.live .free := by rw [he1v]; exact hst
    have hq1 : q.val.store.get "m1".toList = some e1 := by
      rw [hshape]; exact Store.get_set_self _ _ _ hs
    have hqdom : q.val.store.dom = undoWitnessPlan.val.store.dom := by
      rw [hshape]; exact Store.dom_set _ _ _ hs
    have hne : "m2".toList ≠ "m1".toList := by decide
    have hq2eq : q.val.store.get "m2".toList
        = undoWitnessPlan.val.store.get "m2".toList := by
      rw [hshape]; exact Store.get_set_other _ _ _ _ hs hne
    -- any single-slot command mapping `q` back must rewrite `^m1` from `e1` to `e`
    have hback : ∀ (i' : Id) (f : Entity → Except KErr Entity),
        q.mapAt i' f = .ok undoWitnessPlan → f e1 = .ok e := by
      intro i' f hap
      obtain ⟨a, a', hs', hga, hfa, hsh⟩ := mapAt_ok_shape q undoWitnessPlan i' f hap
      by_cases hii : "m1".toList = i'
      · subst hii
        rw [hq1] at hga
        have hpa : undoWitnessPlan.val.store.get "m1".toList = some a' := by
          rw [hsh]; exact Store.get_set_self _ _ _ hs'
        rw [hgetE] at hpa
        rw [(Option.some.inj hga).symm, (Option.some.inj hpa).symm] at hfa
        exact hfa
      · exfalso
        have hgg : undoWitnessPlan.val.store.get "m1".toList
            = q.val.store.get "m1".toList := by
          rw [hsh]; exact Store.get_set_other _ _ _ _ hs' hii
        rw [hgetE, hq1] at hgg
        have hdoc : e.val.live.doc = e1.val.live.doc := by
          rw [Option.some.inj hgg]
        rw [hml, he1live] at hdoc
        simp at hdoc
    -- seven shapes, one refuted observable each
    cases hcmd : inv (.move "m1".toList 1) with
    | move i' d' =>
      rw [hcmd] at hcon
      cases hrd' : resolveDest q.val d' with
      | error k' => simp only [applyCmd, hrd'] at hcon; simp at hcon
      | ok dd =>
        simp only [applyCmd, hrd', cmdMove] at hcon
        have h := hback i' _ hcon
        unfold moveTo at h
        have hev := lift_roundtrips _ _ h
        have hsl : e.val.live = ⟨dd.ix, freshRank q.val dd.ix⟩ := by rw [hev]; rfl
        rw [hml] at hsl
        have hdix : (0 : Nat) = dd.ix := congrArg Site.doc hsl
        have hrk : (1 : Nat) = freshRank q.val dd.ix := congrArg Site.rank hsl
        rw [← hdix] at hrk
        -- but `^m2`'s line survives in document 0 at rank 2, so freshRank ≥ 3
        cases hg2 : undoWitnessPlan.val.store.get "m2".toList with
        | none =>
          have h2 := (by decide :
            (undoWitnessPlan.val.store.get "m2".toList).isSome = true)
          rw [hg2] at h2; simp at h2
        | some e2 =>
          have hm2 : e2.val.live = ⟨0, 2⟩ := by
            have h2 := (by decide : (undoWitnessPlan.val.store.get "m2".toList).map
              (fun x : Entity => x.val.live) = some ⟨0, 2⟩)
            rw [hg2] at h2; simpa using h2
          have hq2 : q.val.store.get "m2".toList = some e2 := by rw [hq2eq, hg2]
          have hlt := freshRank_gt q.val 0 _
            (live_line_mem q.val "m2".toList e2 hq2) (by rw [hm2])
          have hlt2 : e2.val.live.rank < freshRank q.val 0 := hlt
          rw [hm2, ← hrk] at hlt2
          simp at hlt2
    | drop i' =>
      rw [hcmd] at hcon
      simp only [applyCmd, cmdDrop] at hcon
      have h := hback i' _ hcon
      have he : drop e1 = e := Except.ok.inj h
      have hdoc : e.val.live.doc = e1.val.live.doc := by rw [← he]; rfl
      rw [hml, he1live] at hdoc
      simp at hdoc
    | est i' v' =>
      rw [hcmd] at hcon
      simp only [applyCmd, cmdSetEst, cmdEdit] at hcon
      have h := hback i' _ hcon
      unfold editE at h
      split at h
      · injection h
      · have hdoc : e.val.live.doc = e1.val.live.doc := by
          rw [← Except.ok.inj h]
        rw [hml, he1live] at hdoc
        simp at hdoc
    | edit i' v' =>
      rw [hcmd] at hcon
      simp only [applyCmd, cmdEdit] at hcon
      have h := hback i' _ hcon
      unfold editE at h
      split at h
      · injection h
      · have hdoc : e.val.live.doc = e1.val.live.doc := by
          rw [← Except.ok.inj h]
        rw [hml, he1live] at hdoc
        simp at hdoc
    | unset i' k' =>
      rw [hcmd] at hcon
      simp only [applyCmd, cmdUnset] at hcon
      have h := hback i' _ hcon
      unfold unsetE at h
      split at h
      · injection h
      · split at h
        · have hdoc : e.val.live.doc = e1.val.live.doc := by
            rw [← Except.ok.inj h]
          rw [hml, he1live] at hdoc
          simp at hdoc
        · injection h
    | demote i' d' st' =>
      rw [hcmd] at hcon
      cases hrd' : resolveDest q.val d' with
      | error k' => simp only [applyCmd, hrd'] at hcon; simp at hcon
      | ok dd =>
        simp only [applyCmd, hrd', cmdDemote] at hcon
        have h := hback i' _ hcon
        have hev := demote_roundtrips _ _ _ _ h
        have hae : e.val.archive = some ⟨e1.val.live, e1.val.line⟩ := by rw [hev]
        rw [har] at hae
        simp at hae
    | readopt i' d' =>
      rw [hcmd] at hcon
      cases hrd' : resolveDest q.val d' with
      | error k' => simp only [applyCmd, hrd'] at hcon; simp at hcon
      | ok dd =>
        simp only [applyCmd, hrd', cmdReadopt] at hcon
        have h := hback i' _ hcon
        rw [readopt_of_a_live_record_is_refused _ _
          (by rw [he1st]; decide)] at h
        simp at h
    | rank i' n' =>
      rw [hcmd] at hcon
      simp only [applyCmd, cmdRank] at hcon
      have h := hback i' _ hcon
      unfold setRankE at h
      have hev := lift_roundtrips _ _ h
      have hdoc : e.val.live.doc = e1.val.live.doc := by rw [hev]
      rw [hml, he1live] at hdoc
      simp at hdoc
    | add s' d' t' =>
      rw [hcmd] at hcon
      cases hrd' : resolveDest q.val d' with
      | error k' => simp only [applyCmd, hrd'] at hcon; simp at hcon
      | ok dd =>
        simp only [applyCmd, hrd'] at hcon
        unfold WfPlan.insertFresh at hcon
        split at hcon
        · injection hcon with hcon
          have hdl := congrArg (fun w : WfPlan => w.val.store.dom.length) hcon
          simp only [Store.dom_insertFresh, List.length_cons] at hdl
          rw [hqdom] at hdl
          omega
        · simp at hcon

/-! ## §5.8 for the widened `edit` — the wire forms, both directions

The keyed edit's entity-level laws live in Cmd.lean next to `editE`; these are
the same claims about the code the FFI runs — `applyCmd` on `ReqCmd.edit` /
`ReqCmd.unset` / the standing `ReqCmd.est` — plus the named parse-tier
refusals, `parseCmd_rejects_add_title_variants`-style. -/

/-- The standing `est` op **is** the keyed edit at `.est` — one path, one
guard, one reader.  Definitional, so the two can never drift apart. -/
theorem the_est_op_is_the_keyed_est_edit (i : Id) (v : Nat) (p : WfPlan) :
    applyCmd (.est i v) p
      = applyCmd (.edit i (.est ⟨Field.Dur.simple v Field.DurUnit.minutes, rfl⟩)) p := rfl

/-- **Gap 32's check bites on the wire**: a keyed edit addressed to a line
whose raw bytes carry a tab is refused as `tabbedLine`, whatever the key and
value, and nothing is written. -/
theorem edit_of_a_tabbed_line_is_refused (p : WfPlan) (i : Id) (e : Entity) (v : EditVal)
    (hget : p.val.store.get i = some e) (htab : lineHasTab e.val.line = true) :
    applyCmd (.edit i v) p = .error .tabbedLine := by
  show p.mapAt i (editE v) = .error .tabbedLine
  unfold WfPlan.mapAt
  split
  · rename_i hn; rw [hget] at hn; simp at hn
  · rename_i a hget'
    rw [hget] at hget'
    injection hget' with hget'
    subst hget'
    rw [editE_refuses_a_tabbed_line v _ htab]

/-- **And the `est` op is behind the same guard.**  This is the one behaviour
change to a shipped op, taken deliberately and on the refusal side only: the
un-guarded `est` was the kernel writing the *second* `est:` of a line whose
tab hid the first — the S2 shape, in the shipped operation (gap 32). -/
theorem est_of_a_tabbed_line_is_refused (p : WfPlan) (i : Id) (e : Entity) (v : Nat)
    (hget : p.val.store.get i = some e) (htab : lineHasTab e.val.line = true) :
    applyCmd (.est i v) p = .error .tabbedLine :=
  edit_of_a_tabbed_line_is_refused p i e
    (.est ⟨Field.Dur.simple v Field.DurUnit.minutes, rfl⟩) hget htab

/-- The unset guard, on the wire. -/
theorem unset_of_a_tabbed_line_is_refused (p : WfPlan) (i : Id) (e : Entity) (k : EditKey)
    (hget : p.val.store.get i = some e) (htab : lineHasTab e.val.line = true) :
    applyCmd (.unset i k) p = .error .tabbedLine := by
  show p.mapAt i (unsetE k) = .error .tabbedLine
  unfold WfPlan.mapAt
  split
  · rename_i hn; rw [hget] at hn; simp at hn
  · rename_i a hget'
    rw [hget] at hget'
    injection hget' with hget'
    subst hget'
    rw [unsetE_refuses_a_tabbed_line k _ htab]

/-- §5.7 at the wire: unsetting a key the line does not carry is `keyAbsent`,
not a success that removed nothing. -/
theorem unset_of_an_absent_key_is_refused (p : WfPlan) (i : Id) (e : Entity) (k : EditKey)
    (hget : p.val.store.get i = some e) (htab : lineHasTab e.val.line = false)
    (hkey : Field.hasKeyTok k.val e.val.line = false) :
    applyCmd (.unset i k) p = .error .keyAbsent := by
  show p.mapAt i (unsetE k) = .error .keyAbsent
  unfold WfPlan.mapAt
  split
  · rename_i hn; rw [hget] at hn; simp at hn
  · rename_i a hget'
    rw [hget] at hget'
    injection hget' with hget'
    subst hget'
    rw [unset_of_a_key_the_line_does_not_carry_is_refused k _ htab hkey]

/-- **The tab hypothesis is satisfiable on this kernel's own loader** — the
guard is a check something real can fail, not decoration.  A week file whose
item line carries a tab inside a word loads whole (`Text.isSp` is space-only,
so the tab is a word character), and the loaded entity trips `lineHasTab`. -/
def tabbedWitnessDoc : ReqDoc :=
  ⟨"week/2026-W37.md", some ⟨week, 35⟩,
    ["# Tasks".toList, "- [ ] 5 6b Finish\tthe report ^m1".toList]⟩

theorem the_tab_guard_is_not_vacuous :
    (match loadPlan [tabbedWitnessDoc] with
     | .ok p => (p.val.store.get "m1".toList).map (fun e => lineHasTab e.val.line)
     | .error _ => none) = some true := by decide

/-- **The complement (§5.8): a tabless line is not refused on that ground.**
`cmdMove_succeeds`' mirror for the keyed edit: the edit moves no placement, so
`normalized_after_edit` discharges the rank conjunct outright and what stays a
hypothesis is `itemsWfButRanks` — the six conjuncts an edit can genuinely
break (a `min:` whose rate re-parses is still subject to `shapesWf`, say).
Combined with `the_edit_path_writes_what_the_field_path_reads` (Cmd.lean) the
post-state's field view reads exactly the value the wire carried. -/
theorem applyCmd_edit_succeeds (p : WfPlan) (i : Id) (e : Entity) (v : EditVal)
    (hget : p.val.store.get i = some e) (htab : lineHasTab e.val.line = false)
    (hrest : ∀ hs : (p.val.store.get i).isSome = true,
      itemsWfButRanks { p.val with store := p.val.store.set i (⟨{ e.val with line := setVal v e.val.line }, e.property⟩ : Entity) hs } = true) :
    ∃ q : WfPlan, applyCmd (.edit i v) p = .ok q ∧
      q.val.store.get i = some ⟨{ e.val with line := setVal v e.val.line }, e.property⟩ := by
  have hf := editE_ok_of_tabless v e htab
  have hdom : i ∈ p.val.store.dom := (p.val.store.domSpec i).mpr (by rw [hget]; rfl)
  have hore := List.all_eq_true.1 (planWf_parts p.property).2.2.2.1 i hdom
  rw [hget] at hore
  have hor : demotionOriented p.val
      (⟨{ e.val with line := setVal v e.val.line }, e.property⟩ : Entity) = true := hore
  have hin : entityInRange p.val
      (⟨{ e.val with line := setVal v e.val.line }, e.property⟩ : Entity) = true :=
    entityInRange_of_mem p i e hget
  obtain ⟨q, hq, hqi, _⟩ := mapAt_ok_of_inRange p i (editE v) e _ hget hf hin hor
    (fun hs => itemsWf_of_normalized _
      (normalized_after_edit p i e _ hs hget rfl rfl) (hrest hs))
  exact ⟨q, hq, hqi⟩

/-- The same, for the standing `est` op — the success form it never had. -/
theorem applyCmd_est_succeeds (p : WfPlan) (i : Id) (e : Entity) (v : Nat)
    (hget : p.val.store.get i = some e) (htab : lineHasTab e.val.line = false)
    (hrest : ∀ hs : (p.val.store.get i).isSome = true,
      itemsWfButRanks { p.val with store := p.val.store.set i (⟨{ e.val with line := setVal (.est ⟨Field.Dur.simple v Field.DurUnit.minutes, rfl⟩) e.val.line }, e.property⟩ : Entity) hs } = true) :
    ∃ q : WfPlan, applyCmd (.est i v) p = .ok q ∧
      q.val.store.get i = some ⟨{ e.val with line := setVal (.est ⟨Field.Dur.simple v Field.DurUnit.minutes, rfl⟩) e.val.line }, e.property⟩ :=
  applyCmd_edit_succeeds p i e _ hget htab hrest

/-- And the unset success form: present key, tabless line, the removal lands
and the store holds exactly the filtered line. -/
theorem applyCmd_unset_succeeds (p : WfPlan) (i : Id) (e : Entity) (k : EditKey)
    (hget : p.val.store.get i = some e) (htab : lineHasTab e.val.line = false)
    (hkey : Field.hasKeyTok k.val e.val.line = true)
    (hrest : ∀ hs : (p.val.store.get i).isSome = true,
      itemsWfButRanks { p.val with store := p.val.store.set i (⟨{ e.val with line := Field.unsetKey k.val e.val.line }, e.property⟩ : Entity) hs } = true) :
    ∃ q : WfPlan, applyCmd (.unset i k) p = .ok q ∧
      q.val.store.get i = some ⟨{ e.val with line := Field.unsetKey k.val e.val.line }, e.property⟩ := by
  have hf := unsetE_ok_of_present k e htab hkey
  have hdom : i ∈ p.val.store.dom := (p.val.store.domSpec i).mpr (by rw [hget]; rfl)
  have hore := List.all_eq_true.1 (planWf_parts p.property).2.2.2.1 i hdom
  rw [hget] at hore
  have hor : demotionOriented p.val
      (⟨{ e.val with line := Field.unsetKey k.val e.val.line }, e.property⟩ : Entity) = true :=
    hore
  have hin : entityInRange p.val
      (⟨{ e.val with line := Field.unsetKey k.val e.val.line }, e.property⟩ : Entity) = true :=
    entityInRange_of_mem p i e hget
  obtain ⟨q, hq, hqi, _⟩ := mapAt_ok_of_inRange p i (unsetE k) e _ hget hf hin hor
    (fun hs => itemsWf_of_normalized _
      (normalized_after_edit p i e _ hs hget rfl rfl) (hrest hs))
  exact ⟨q, hq, hqi⟩

/-- §5.7's parse-tier refusals for the keyed edit, each by name: a spelling
that is no key, a key not yet wired (README gap 40), and two values the field
grammars refuse — `ci:7` is the `Fin 6` smart constructor biting (R10), and
`est=3d` is `NdDur` refusing a day-carrying estimate. -/
theorem parseCmd_rejects_edit_variants :
    parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "size".toList), ("value".toList, .str "3".toList)]) = .error "unknownKey size" ∧
    parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "due".toList), ("value".toList, .str "2026-09-20".toList)]) = .error "keyNotWired due" ∧
    parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "ci".toList), ("value".toList, .str "7".toList)]) = .error "badValue ci" ∧
    parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "est".toList), ("value".toList, .str "3d".toList)]) = .error "badValue est" :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The positive parse forms are not vacuous: a keyed value lands as `.edit`
with the key it named, and an empty value is the unset form. -/
theorem parseCmd_reads_the_keyed_edit_forms :
    ((match parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "pref".toList), ("value".toList, .str "07:30".toList)]) with
      | .ok (.edit i v) => i == "t3".toList && v.key == Field.Key.pref
      | _ => false) &&
     (match parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "est".toList), ("value".toList, .str "".toList)]) with
      | .ok (.unset i k) => i == "t3".toList && k.val == Field.Key.est
      | _ => false)) = true := by decide

/-! ## J5, the response side: `call` writes the kernel's own `JVal` with `jemit`

Every response builder above (`jsonErr`, `lerrJson`, `regionJson`, `loadPlan`'s
refusals, `runPlan`) now returns a `JVal`, and `call` emits it with
`String.ofList ∘ jemit` — `Json.compress` is gone from the response path.  The
one wire-visible byte change is **key order**: an assoc list keeps build order,
where `Json.mkObj` sorted.  The shapes and every other byte are unchanged; the
README's J5 block carries the differential measurement.  These two pin the new
order at the builders the FFI calls, so a reorder is a proof failure and not
only a Rust-test failure. -/

/-- **The response shapes, byte for byte, in build order.**  The free-text
`err`, a `kernel` refusal, and an `ok` document — `path`, then `lines`, then the
region's `grain` and `ix` — with a quote in the line so the escaping is on the
path being pinned.  Small by design (the Json.lean memory rule): emission is
evaluated, never a parser run. -/
theorem the_response_shapes_emit_in_build_order :
    jemit (jsonErr "unknown op fly") = "{\"err\":\"unknown op fly\"}".toList ∧
    jemit (jone "err" (jone "kernel" (.str "noSuchId".toList)))
      = "{\"err\":{\"kernel\":\"noSuchId\"}}".toList ∧
    jemit (jone "ok" (jone "docs" (.arr [.obj ([("path".toList, .str "w.md".toList),
        ("lines".toList, .arr [.str "- [ ] a \"q\" ^x1".toList])] ++ regionJson (some ⟨1, 35⟩))])))
      = "{\"ok\":{\"docs\":[{\"path\":\"w.md\",\"lines\":[\"- [ ] a \\\"q\\\" ^x1\"],\"grain\":1,\"ix\":35}]}}".toList := by
  decide

/-- `badLine`'s three keys go out as `path`, `line`, `why` — the order written
in `lerrJson`, not `mkObj`'s `line`, `path`, `why`.  Stated for every diagnostic
rather than by evaluation, because `why` is a `repr` the kernel does not reduce
cheaply. -/
theorem the_bad_line_diagnostic_keys_in_build_order (pa : List Char) (n : Nat) (w : PErr) :
    lerrJson (.badLine pa n w) = jone "badLine" (.obj [("path".toList, .str pa),
      ("line".toList, .num n), ("why".toList, .str (toString (repr w)).toList)]) := rfl

/-! ## J5, the request side, and J6: the JSON edge is the kernel's, both ways

`call` reads the request with `jparse` over `input.toList`, and every field
through `jget`; no kernel module imports `Lean.Data.Json` any more.  Reading
over the kernel's own value changed three rules, each now a named refusal rather
than a silent choice: a **duplicate key** that is read (`jget`, §5.6 — the old
reader, like serde_json, kept the last); a **`cmds` that is present but not an
array** (the old reader swallowed it as no commands, §5.7); and a **`grain`
carried twice** on a document or a `demote`.  A parse refusal is `bad json: `
plus `jerrText`'s constructor name.  `respond` is the response *value* and
`call` is `respond`, emitted — which is what makes the last two theorems below
statements about the exported function's bytes. -/

/-- **A field read twice is refused by name**, whichever field it is, and the
same command with the field once reads.  §5.8: the rule bites and does not
over-bite. -/
theorem parseCmd_refuses_a_duplicate_field :
    parseCmd (.obj [("op".toList, .str "drop".toList), ("id".toList, .str "a".toList),
        ("id".toList, .str "b".toList)]) = .error "duplicateKey id" ∧
    parseCmd (.obj [("op".toList, .str "drop".toList), ("op".toList, .str "move".toList),
        ("id".toList, .str "a".toList)]) = .error "duplicateKey op" ∧
    parseCmd (.obj [("op".toList, .str "drop".toList), ("id".toList, .str "a".toList)])
      = .ok (.drop "a".toList) :=
  ⟨rfl, rfl, rfl⟩

/-- **A `cmds` that is not an array is refused**, not read as a request with no
commands — which would answer `ok` with every document unchanged, and let the
host believe a command it sent had applied. -/
theorem run_refuses_cmds_that_are_not_an_array :
    run (.obj [("docs".toList, .arr []), ("cmds".toList, .num 3)])
      = .error (jsonErr "array expected") := rfl

/-- **A parse refusal reaches the host by name** — here `expectedKey` and the
surrogate escape README gap 42 refuses — over explicit `List Char` inputs (the
Json.lean memory rule: a parser run is small and never over a string literal's
`toList`). -/
theorem respond_names_a_parse_refusal :
    respond ['{', ' ', 'n'] = jsonErr "bad json: expectedKey n" ∧
    respond ['"', '\\', 'u', 'd', '8', '3', 'd', '"']
      = jsonErr "bad json: badEscape surrogateEscape 55357" :=
  ⟨rfl, rfl⟩

/-- **P\*, stage 3, README gap 6: the JSON edge round-trips — at the exported
function.**  Whatever bytes `call` hands the host, the kernel's own parser reads
back to exactly the response value `respond` built: no fragment restriction and
no hypothesis on the input, well-formed or not.  This **discharges Goals.lean's
`the_json_edge_round_trips` by the narrowing its doc comment licensed**: that
goal was stated over `Lean.Json.parse ∘ Lean.Json.compress`, whose `partial
def`s make it neither provable nor refutable (README "Gap 39 REPRICED"), and
whose own route was "a kernel-owned emitter and fuel-structural parser …
round-tripped unconditionally, put on the wire in `call`".  Both halves of that
are now true: `jparse_jemit` is the unconditional round trip over every `JVal`,
and this is its instance at the code `callExport` runs.  What it does not say,
and nothing here can: that the **host's** reader (serde_json in
`kernel_bridge.rs`, the hand-written codec in the corpus harness) agrees with
`jparse` — that is corpus and FFI evidence, the framing gap 12 took for Rust's
`split('\n')`. -/
theorem the_response_call_emits_parses_back (input : String) :
    jparse (call input).toList = .ok (respond input.toList) := by
  unfold call
  rw [String.toList_ofList]
  exact jparse_jemit _

/-- **Not vacuous, and end to end: the FFI test `duplicate_ids_are_rejected_at_load`
as a theorem about `call`.**  The request bytes are the test's, verbatim
(`demoRequestBytes`); the response is the bytes the test asserts
(`demoResponseBytes`).  The parse is `the_real_request_bytes_round_trip` (an
instance of `jparse_jemit`, not a parser run over a literal), the loader's
refusal is evaluated, and the emission is `the_real_response_bytes_round_trip`. -/
theorem call_refuses_the_real_duplicate_id_request :
    call (String.ofList demoRequestBytes) = String.ofList demoResponseBytes := by
  have hrun : run demoRequest = .error demoResponse := rfl
  unfold call respond
  rw [String.toList_ofList, the_real_request_bytes_round_trip.2]
  simp only [hrun]
  rw [the_real_response_bytes_round_trip.1]

end Tm
