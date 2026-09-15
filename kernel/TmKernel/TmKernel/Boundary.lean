import TmKernel.Report
import TmKernel.Json
import TmKernel.Tree
import TmKernel.Priority
import TmKernel.Capacity
import TmKernel.Log
import TmKernel.Lookahead
import TmKernel.Replay
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
  /-- an HTML comment opened on line `n` (0-based, as `badLine`) is still open at
      the end of the file.  Everything after the opener would be prose, and the
      kernel does not guess where the writer meant the comment to stop. -/
  | unterminatedComment (path : List Char) (n : Nat)
deriving Repr

/-! ### Rejection is real

A line that *looks* like an item and does not parse used to be silently
reclassified as prose: `- [Z] x ^a1` and `- [ ] two ^a1 ^a2` were accepted, kept
and written back, and `LErr.badLine` was dead code.  "Accept or reject" is the
whole contract of a boundary, so the scan below is run before anything is
built, and only `PErr.notAnItem` — the line does not have an item's shape at
all — counts as prose. -/

/-- The scan, from comment state `o` — `some n` while a comment opened on line
`n` is open.  A line read inside a comment is prose whatever its bytes, so a
broken example item in a guidance comment is not a `badLine`; a comment still
open at the end of the file is `unterminatedComment`, naming its opener. -/
def scanLinesFrom (path : List Char) : Option Nat → Nat → List (List Char) → Except LErr Unit
  | none,   _, []      => .ok ()
  | some n, _, []      => .error (.unterminatedComment path n)
  | o, k, l :: rest =>
    let o' := if commentAfter o.isSome l then some (o.getD k) else none
    if o.isSome then scanLinesFrom path o' (k + 1) rest else
    match parseItem l with
    | .ok _             => scanLinesFrom path o' (k + 1) rest
    | .error .notAnItem => scanLinesFrom path o' (k + 1) rest
    | .error e          => .error (.badLine path k e)

def scanLines (path : List Char) (k : Nat) (ls : List (List Char)) : Except LErr Unit :=
  scanLinesFrom path none k ls

theorem scan_state_isSome (b : Bool) (n : Nat) :
    (if b then some n else none).isSome = b := by
  cases b <;> rfl

/-- One step of an accepted scan: the tail is accepted from the state the line
leaves, and a line read with no comment open is prose-shaped or an item. -/
theorem scanLinesFrom_cons_ok (path : List Char) (o : Option Nat) (k : Nat) (l : List Char)
    (rest : List (List Char)) (h : scanLinesFrom path o k (l :: rest) = .ok ()) :
    scanLinesFrom path (if commentAfter o.isSome l then some (o.getD k) else none) (k + 1) rest
        = .ok () ∧
      (o.isSome = false → parseItem l = .error .notAnItem ∨ isItemLine l = true) := by
  cases o with
  | some n =>
      refine ⟨?_, fun hs => by simp at hs⟩
      simpa [scanLinesFrom] using h
  | none =>
      simp only [scanLinesFrom, Option.isSome_none, Bool.false_eq_true, if_false] at h
      cases hp : parseItem l with
      | ok t =>
          rw [hp] at h
          exact ⟨h, fun _ => Or.inr (by simp [isItemLine, hp])⟩
      | error e =>
          cases e with
          | notAnItem => rw [hp] at h; exact ⟨h, fun _ => Or.inl rfl⟩
          | badState c => rw [hp] at h; simp at h
          | noId       => rw [hp] at h; simp at h
          | manyIds    => rw [hp] at h; simp at h

theorem scanLinesFrom_prose (path : List Char) (o : Option Nat) (k : Nat)
    (ls : List (List Char)) (h : scanLinesFrom path o k ls = .ok ()) :
    ∀ q ∈ (splitDocC o.isSome k ls).prose,
      commentOpenFrom o.isSome (splitDocC o.isSome k ls).prose q.1 = false →
      parseItem q.2 = .error .notAnItem := by
  induction ls generalizing o k with
  | nil => intro q hq; simp [splitDocC] at hq
  | cons l rest ih =>
      obtain ⟨hrest, hhead⟩ := scanLinesFrom_cons_ok path o k l rest h
      have ihr := ih _ (k + 1) hrest
      rw [scan_state_isSome] at ihr
      intro q hq hco
      rcases splitDocC_cons o.isSome k l rest with ⟨hs, hor⟩ | ⟨i, g, r, hc, hp, hs⟩
      · rw [hs] at hq hco
        dsimp only at hq hco
        have hge := splitDocC_prose_ge (commentAfter o.isSome l) (k + 1) rest
        rcases List.mem_cons.1 hq with hqe | hq'
        · subst hqe
          rw [commentOpenFrom_none_below _ _ k (by
            intro x hx
            rcases List.mem_cons.1 hx with hxe | hx'
            · subst hxe; exact Nat.le_refl _
            · have := hge x hx'; omega)] at hco
          rcases hhead hco with h1 | h1
          · exact h1
          · rcases hor with h2 | h2
            · rw [hco] at h2; exact absurd h2 (by decide)
            · rw [h1] at h2; exact absurd h2 (by decide)
        · have hk : k < q.1 := by have := hge q hq'; omega
          rw [commentOpenFrom_cons_below _ k l _ q.1 hk] at hco
          exact ihr q hq' hco
      · rw [hs] at hq hco
        dsimp only at hq hco
        have hc' : commentAfter false l = false :=
          commentAfter_false_of_item l (by simp [isItemLine, hp])
        simp only [hc, hc'] at hco ihr hq
        exact ihr q hq hco

/-- What acceptance buys: every prose line of an accepted document that is
**not inside a comment** failed to parse because it is not an item line, not
because it is a broken one.  (Supersedes `scanLines_prose`, 2026-09-12: a line
inside a comment is prose whatever its bytes, broken item shapes included.) -/
theorem scanLines_prose_outside_a_comment (path : List Char) (k : Nat) (ls : List (List Char))
    (h : scanLines path k ls = .ok ()) :
    ∀ q ∈ (splitDoc k ls).prose,
      inComment (splitDoc k ls).prose q.1 = false → parseItem q.2 = .error .notAnItem :=
  scanLinesFrom_prose path none k ls h

theorem scanLinesFrom_closes (path : List Char) (o : Option Nat) (k : Nat)
    (ls : List (List Char)) (h : scanLinesFrom path o k ls = .ok ()) :
    ls.foldl commentAfter o.isSome = false := by
  induction ls generalizing o k with
  | nil =>
      cases o with
      | none => rfl
      | some n => simp [scanLinesFrom] at h
  | cons l rest ih =>
      obtain ⟨hrest, _⟩ := scanLinesFrom_cons_ok path o k l rest h
      have := ih _ (k + 1) hrest
      rw [scan_state_isSome] at this
      simpa [List.foldl_cons] using this

/-- **The unterminated-comment decision, as a theorem.**  Every document the
scan accepts ends with no comment open: reading its lines through
`commentAfter` from the top leaves the state closed.  The refusal it rules in is
`LErr.unterminatedComment`, witnessed by `an_unterminated_comment_is_refused`. -/
theorem scanLines_accepts_only_closed_comments (path : List Char) (k : Nat)
    (ls : List (List Char)) (h : scanLines path k ls = .ok ()) :
    ls.foldl commentAfter false = false :=
  scanLinesFrom_closes path none k ls h

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

/-! ### `dedupIds` with a seen-set (`@[csimp]`)

`dedupIds` asks `i ∈ dedupIds rest` for every id, a scan of the list so far: `n²/2`
`List Char` comparisons.  `dedupIdsFast` runs the same right fold and answers the
membership question from an `IdMap` of the ids already seen; `dedupStep_fold` is
the simulation, and the equality is the `csimp` lemma. -/

/-- One step of the right fold.  The pair is taken apart and the lookup is the
`match`'s scrutinee, so the table reaches `insert` with no other reference and
is updated in place rather than copied (`dedupStep_eq` is the plain reading). -/
def dedupStep : Id → IdMap Unit × List Id → IdMap Unit × List Id
  | i, (t, out) =>
    match (t.get i).isSome with
    | true  => (t, out)
    | false => (t.insert i (), i :: out)

theorem dedupStep_eq (i : Id) (acc : IdMap Unit × List Id) :
    dedupStep i acc = if (acc.1.get i).isSome then acc else (acc.1.insert i (), i :: acc.2) := by
  rcases acc with ⟨t, out⟩
  simp only [dedupStep]
  cases (t.get i).isSome <;> rfl

theorem dedupStep_fold (n : Nat) : ∀ (l : List Id),
    0 < (l.foldr dedupStep (IdMap.empty n, [])).1.buckets.size ∧
    (∀ j, ((l.foldr dedupStep (IdMap.empty n, [])).1.get j).isSome = decide (j ∈ l)) ∧
    (l.foldr dedupStep (IdMap.empty n, [])).2 = dedupIds l
  | [] => ⟨IdMap.size_empty n, fun j => by simp [IdMap.get_empty], rfl⟩
  | i :: rest => by
    obtain ⟨hp, hg, hd⟩ := dedupStep_fold n rest
    simp only [List.foldr_cons]
    generalize List.foldr dedupStep (IdMap.empty n, []) rest = acc at hp hg hd
    have hmem : i ∈ dedupIds rest ↔ i ∈ rest := mem_dedupIds rest i
    rw [dedupStep_eq]
    by_cases hc : (acc.1.get i).isSome = true
    · have hi : i ∈ rest := by simpa [hg i] using hc
      simp only [hc, if_true]
      refine ⟨hp, fun j => ?_, ?_⟩
      · rw [hg j]
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
      · rw [dedupIds_cons, if_pos (hmem.2 hi), hd]
    · have hi : i ∉ rest := by
        intro h; exact hc (by simpa [hg i] using h)
      simp only [hc, if_false, Bool.false_eq_true]
      refine ⟨by simpa [IdMap.size_insert] using hp, fun j => ?_, ?_⟩
      · rw [IdMap.get_insert _ _ _ _ hp]
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj, hg j]
      · rw [dedupIds_cons, if_neg (fun h => hi (hmem.1 h)), hd]

def dedupIdsFast (l : List Id) : List Id := (l.foldr dedupStep (IdMap.empty l.length, [])).2

@[csimp] theorem dedupIds_eq_dedupIdsFast : @dedupIds = @dedupIdsFast := by
  funext l; exact (dedupStep_fold l.length l).2.2.symm

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

/-! ### `buildEntities` from one grouping pass (`@[csimp]`)

`buildEntities` filters every placement once per id (`n²`) and appends each entity
to the end of its accumulator (`n²` again).  `buildEntitiesFast` groups the
placements by id in one right fold, in their original order (`groupStep_fold`),
and maps over the ids; `foldlM_snoc_eq_mapM` says the snoc-fold is that map. -/

def groupStep (q : Placement) (t : IdMap (List Placement)) : IdMap (List Placement) :=
  t.insert q.id (q :: (t.get q.id).getD [])

theorem groupStep_fold (n : Nat) : ∀ (ps : List Placement),
    0 < (ps.foldr groupStep (IdMap.empty n)).buckets.size ∧
    ∀ i, ((ps.foldr groupStep (IdMap.empty n)).get i).getD [] = ps.filter (fun q => q.id == i)
  | [] => ⟨IdMap.size_empty n, fun i => by simp [IdMap.get_empty]⟩
  | q :: rest => by
    obtain ⟨hp, hg⟩ := groupStep_fold n rest
    simp only [List.foldr_cons]
    generalize List.foldr groupStep (IdMap.empty n) rest = t at hp hg
    refine ⟨by simpa [groupStep, IdMap.size_insert] using hp, fun i => ?_⟩
    simp only [groupStep, IdMap.get_insert _ _ _ _ hp, List.filter_cons]
    by_cases hi : i = q.id
    · subst hi; simp [hg]
    · have : (q.id == i) = false := by simpa using Ne.symm hi
      simp [hi, hg i, this]

def buildEntitiesFast (ps : List Placement) : Except LErr (List (Id × Entity)) :=
  let g := ps.foldr groupStep (IdMap.empty ps.length)
  (dedupIds (ps.map Placement.id)).mapM (fun i => do
    let e ← buildEntity i ((g.get i).getD [])
    pure (i, e))

theorem foldlM_snoc_eq_mapM (F : Id → Except LErr Entity) : ∀ (ids : List Id) (acc : List (Id × Entity)),
    ids.foldlM (fun acc i => do let e ← F i; pure (acc ++ [(i, e)])) acc =
      (do let r ← ids.mapM (fun i => do let e ← F i; pure (i, e)); pure (acc ++ r))
  | [], acc => by simp
  | i :: rest, acc => by
    simp only [List.foldlM_cons, List.mapM_cons]
    cases F i with
    | error x => rfl
    | ok e =>
      show rest.foldlM _ (acc ++ [(i, e)]) = _
      rw [foldlM_snoc_eq_mapM F rest (acc ++ [(i, e)])]
      cases rest.mapM (fun i => do let e ← F i; pure (i, e)) with
      | error x => rfl
      | ok r =>
        show (Except.ok (acc ++ [(i, e)] ++ r) : Except LErr _) = Except.ok (acc ++ (i, e) :: r)
        simp

@[csimp] theorem buildEntities_eq_buildEntitiesFast : @buildEntities = @buildEntitiesFast := by
  funext ps
  have hg := (groupStep_fold ps.length ps).2
  simp only [buildEntities, buildEntitiesFast, hg]
  refine (foldlM_snoc_eq_mapM (fun i => buildEntity i (ps.filter (fun q => q.id == i))) _ []).trans ?_
  cases (dedupIds (ps.map Placement.id)).mapM
      (fun i => do let e ← buildEntity i (ps.filter (fun q => q.id == i)); pure (i, e)) with
  | error x => rfl
  | ok r => simp

def loadStore (items : List (Id × Entity)) : Store :=
  items.foldl (fun s p => s.insert p.1 p.2) emptyStore

/-! ### The loader's store, with its lookup built once (`@[csimp]`)

`loadStore` is the definition the loader's theorems read; its `get` is a chain
of one closure per item, so every lookup walks the chain.  `loadStoreFast` is the
same store — the same `dom`, list for list, and a `get` equal at every id — with
the lookups answered from an `IdMap` filled by the same fold
(`loadStep_fold` is the simulation).  The `csimp` lemma makes the compiled
loader build that one; no theorem about `loadStore` changes (Fast.lean's header
says why this is not `implemented_by`). -/

/-- One step of the loader's fold, over a table and the domain so far.  As in
`dedupStep`, the lookup is decided before the table is touched, so the table is
updated in place; `loadStep_eq` is the plain reading. -/
def loadStep : IdMap Entity × List Id → Id × Entity → IdMap Entity × List Id
  | (t, dom), (i, e) =>
    match (t.get i).isSome with
    | true  => (t.insert i e, dom)
    | false => (t.insert i e, i :: dom)

theorem loadStep_eq (acc : IdMap Entity × List Id) (q : Id × Entity) :
    loadStep acc q = (acc.1.insert q.1 q.2, if (acc.1.get q.1).isSome then acc.2 else q.1 :: acc.2) := by
  rcases acc with ⟨t, dom⟩; rcases q with ⟨i, e⟩
  simp only [loadStep]
  cases (t.get i).isSome <;> rfl

theorem loadStep_fold : ∀ (items : List (Id × Entity)) (s : Store) (acc : IdMap Entity × List Id),
    0 < acc.1.buckets.size → (∀ j, acc.1.get j = s.get j) → acc.2 = s.dom →
    0 < (items.foldl loadStep acc).1.buckets.size ∧
      (∀ j, (items.foldl loadStep acc).1.get j = (items.foldl (fun s p => s.insert p.1 p.2) s).get j) ∧
      (items.foldl loadStep acc).2 = (items.foldl (fun s p => s.insert p.1 p.2) s).dom
  | [], _, _, hp, hg, hd => ⟨hp, hg, hd⟩
  | q :: rest, s, acc, hp, hg, hd => by
    simp only [List.foldl_cons]
    apply loadStep_fold rest (s.insert q.1 q.2) (loadStep acc q)
    · simpa [loadStep_eq, IdMap.size_insert] using hp
    · intro j
      have h1 : (s.insert q.1 q.2).get j = if j = q.1 then some q.2 else s.get j := by
        unfold Store.insert; split <;> rfl
      simp only [loadStep_eq, IdMap.get_insert _ _ _ _ hp, h1, hg]
    · have h1 : (s.insert q.1 q.2).dom = if q.1 ∈ s.dom then s.dom else q.1 :: s.dom := by
        unfold Store.insert; split <;> rfl
      have h2 : (acc.1.get q.1).isSome = decide (q.1 ∈ s.dom) := by
        rw [hg q.1]
        cases h : (s.get q.1).isSome
        · exact (decide_eq_false (fun hm => by rw [(s.domSpec q.1).1 hm] at h; cases h)).symm
        · exact (decide_eq_true ((s.domSpec q.1).2 h)).symm
      simp only [loadStep_eq, h1, h2, hd]
      by_cases hm : q.1 ∈ s.dom <;> simp [hm]

/-- The loader's store, with the lookup table built once. -/
def loadStoreFast (items : List (Id × Entity)) : Store :=
  let r := items.foldl loadStep (IdMap.empty items.length, [])
  have hsim := loadStep_fold items emptyStore (IdMap.empty items.length, [])
    (by simp [IdMap.empty]) (fun j => IdMap.get_empty _ j) rfl
  { get := r.1.get
    dom := r.2
    domSpec := fun i => by
      rw [hsim.2.2, hsim.2.1 i]; exact (loadStore items).domSpec i
    domNodup := by rw [hsim.2.2]; exact (loadStore items).domNodup }

@[csimp] theorem loadStore_eq_loadStoreFast : @loadStore = @loadStoreFast := by
  funext items
  have hsim := loadStep_fold items emptyStore (IdMap.empty items.length, [])
    (by simp [IdMap.empty]) (fun j => IdMap.get_empty _ j) rfl
  exact Store.ext_of (fun j => (hsim.2.1 j).symm) hsim.2.2.symm

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

It used to take a fourth hypothesis, `hpar : e.val.parent = none`: `parent` was
the one §3.1 field still stored, the loader had no way to set it, and with it set
the loader's answer differed from `e` in exactly that slot.  Since D6 `parent` is
a view of the line (README gap 22, closed), the loader's record carries the
line's `@parent` because it carries the line, and the hypothesis is gone — the
statement is strictly stronger under the same name. -/
theorem the_kernel_can_read_the_pairs_it_writes (p : WfPlan) (i : Id) (e : Entity) (t : Tomb)
    (hget : p.val.store.get i = some e) (harch : e.val.archive = some t) :
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
            line := e.val.line } : Core) = e.val
    rw [← harch]
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
  /-- §6.3's close of one grain, at the request's instant, reporting minutes at
      the request's block length.  Both come from the request (`ReqClock`) and
      never from a default: a command that closes cannot be built without them. -/
  | close (g : Grain) (now : Day) (bm : BlockMin)
  /-- §6.3's automatic close — each grain once, coarsest last (`autoClose`). -/
  | autoClose (now : Day) (bm : BlockMin)
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
    -- (`keyNotWired`: only `demoted` since gap 40's bridges), and a value the key's
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

/-! ### The request's instant and block length

**`now` enters the request** (AGENTS §8.2 scope item 4).  A kernel that invented
`now` would close the wrong region silently, so there is no default: `now` is a
`Day` read by the kernel's own date grammar (`Field.parseDate`, whose smart
constructor is `mkDate?` and whose round trip is `parse_render_date`), written
`"now":"2026-09-12"`.  `blockMin` is what `Nb` means in minutes, for the
report's minutes, read through `BlockMin.ofNat?`.

Each is **optional at the request and required by the command that reads it**:
a request that carries neither can still `move` or `drop`, and a `close` or an
`autoClose` in a request that omits one is refused by name — `nowAbsent`,
`blockMinAbsent` — before any document is loaded.  A value that is present and
malformed is refused whatever the commands — `badNow` (not a string, or not a
real `YYYY-MM-DD` date), `badBlockMin` (not a number, or `0`) — never ignored
because nothing happened to read it.  Carried twice, either is `jget`'s
`duplicateKey`. -/
structure ReqClock where
  now      : Option Day
  blockMin : Option BlockMin

def parseClock (j : JVal) : Except String ReqClock := do
  let now ←
    match ← jget j "now" with
    | none => pure none
    | some (.str s) =>
      match Field.parseDate s with
      | some d => pure (some d)
      | none   => throw "badNow"
    | some _ => throw "badNow"
  let bm ←
    match ← jget j "blockMin" with
    | none => pure none
    | some (.num n) =>
      match BlockMin.ofNat? n with
      | some b => pure (some b)
      | none   => throw "badBlockMin"
    | some _ => throw "badBlockMin"
  return ⟨now, bm⟩

def ReqClock.needNow (c : ReqClock) : Except String Day :=
  match c.now with
  | some d => .ok d
  | none   => .error "nowAbsent"

def ReqClock.needBlockMin (c : ReqClock) : Except String BlockMin :=
  match c.blockMin with
  | some b => .ok b
  | none   => .error "blockMinAbsent"

/-- **One command, with the request's clock.**  The two ops that read the clock
are read here; every other op is `parseCmd`'s, unchanged
(`parseCmdAt_is_parseCmd`). -/
def parseCmdAt (c : ReqClock) (j : JVal) : Except String ReqCmd := do
  let op ← getStr j "op"
  match String.ofList op with
  | "close" =>
    let gn ← getNat j "grain"
    match Grain.ofNat? gn with
    | none   => throw s!"grain {gn} out of range (0..{grainCount - 1})"
    | some g => return .close g (← c.needNow) (← c.needBlockMin)
  | "autoClose" => return .autoClose (← c.needNow) (← c.needBlockMin)
  | _ => parseCmd j

def kerrName : KErr → String
  | .occupied       => "occupied"
  | .noSuchId       => "noSuchId"
  | .notDemoted     => "notDemoted"
  | .alreadyDemoted => "alreadyDemoted"
  | .badHorizon     => "badHorizon"
  | .badItem        => "badItem"
  | .tabbedLine     => "tabbedLine"
  | .keyAbsent      => "keyAbsent" | .danglingDep => "danglingDep" | .depCycle => "depCycle"
  | .noTarget       => "noTarget"  | .noSection => "noSection"

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
`freshRank`, no tombstone, `live free` (the `[ ]` box).  Its parent is whatever
`@parent` the title's words carry, read off the line like every field (D6): a
title naming an id the tree does not carry is refused by the post-state's
`planWf` (`danglingParent`), not written. -/
def addCore (p : PlanCore) (dd : Dest p) (i : Id) (title : List Char) : Core :=
  { live := dd.site (freshRank p dd.ix), archive := none, status := .live .free,
    line := { indent := [], toks := addTitleToks title i } }

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

/-- **Where the `demote` verb files its record (gap 20's remainder, stage 4 step 9).**
§6.3: "copies it into `month/<current>#Demoted`".  The spot is the week close's
own — `landingSpot` at `Landing.demotedSection`, the end of the first `# Demoted`
and ahead of the heading after it, with `landAt`'s shift making room — so the
verb and the close cannot disagree about where a record lands
(`demoteSpot_is_the_week_close_landing`).  A destination with no `# Demoted` is
the one place they differ: the close refuses `noSection` (gap 56) and the verb
lands at the end of the file as it always has, because refusing a `[-]` outside
`# Demoted` is AGENTS §10.5 q9, the owner's (README gap 60). -/
def demoteSpot (p : PlanCore) (k : DocIx) : Option Nat :=
  match landingSpot p k .demotedSection none with
  | .ok spot => spot
  | .error _ => none

/-- The verb's landing is the week close's landing wherever the close has one. -/
theorem demoteSpot_is_the_week_close_landing (p : PlanCore) (k : DocIx)
    (src : Option (List Char)) (spot : Option Nat)
    (h : landingSpot p k (closePolicy week).landing src = .ok spot) : demoteSpot p k = spot := by
  unfold demoteSpot
  have hl : (closePolicy week).landing = .demotedSection := rfl
  rw [hl, landingSpot_src p k (by decide) src none] at h
  rw [h]

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
  | .est i v        => nameEditFault p i (.est ⟨Field.Dur.simple v Field.DurUnit.minutes, rfl⟩) (cmdSetEst v i p)
  | .demote i d st =>
    match resolveDest p.val d with
    | .error k => .error k
    | .ok dd   => guardStray ((p.val.store.get i).any (hasAStrayTomb p.val))
                    (landAt p dd.ix (demoteSpot p.val dd.ix) i (fun t e => refile t st e))
  | .readopt i d    =>
    match resolveDest p.val d with
    | .error k => .error k
    | .ok dd   => cmdReadopt i (freshRank p.val dd.ix) p dd
  | .rank i n       => cmdRank i n p
  | .edit i v       => nameEditFault p i v (cmdEdit v i p)
  | .unset i k      => cmdUnset k i p
  | .add seed d title =>
    match resolveDest p.val d with
    | .error k => .error k
    | .ok dd =>
      p.insertFresh (freshId seed p.val.store.dom)
        (addEntity p.val dd (freshId seed p.val.store.dom) title)
        (store_get_isNone_of_not_mem (add_assigns_a_fresh_id seed _))
  | .close g now bm   => close g now bm.val p
  | .autoClose now bm => autoClose now bm.val p

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

/-! ### A request's report

`applyCmdR` is `applyCmd` with each command's report beside the plan: a close
reports its entries (`closeR`, `autoCloseR`), every other command reports
nothing.  `applyAllR_plan` says the reporting form writes exactly what
`applyAll` writes, so every theorem about `applyAll` is a theorem about the plan
the FFI hands back. -/
def applyCmdR (c : ReqCmd) (p : WfPlan) : Except KErr (WfPlan × Report) :=
  match c with
  | .close g now bm   => closeR g now bm p
  | .autoClose now bm => autoCloseR now bm p
  | c                 => (applyCmd c p).map (fun q => (q, Report.empty))

def applyAllR : List ReqCmd → WfPlan → Except KErr (WfPlan × Report)
  | [],      p => .ok (p, Report.empty)
  | c :: cs, p => (applyCmdR c p).bind (fun qr =>
      (applyAllR cs qr.1).map (fun qr' => (qr'.1, qr.2.append qr'.2)))

theorem except_map_pair_fst {α β ε : Type} (x : Except ε α) (b : β) :
    (x.map (fun a => (a, b))).map Prod.fst = x := by
  cases x <;> rfl

theorem applyCmdR_plan (c : ReqCmd) (p : WfPlan) : (applyCmdR c p).map Prod.fst = applyCmd c p := by
  cases c with
  | close g now bm => exact closeR_plan g now bm p
  | autoClose now bm => exact autoCloseR_plan now bm p
  | _ => exact except_map_pair_fst _ _

/-- **Reporting changes nothing a request writes.** -/
theorem applyAllR_plan : ∀ (cs : List ReqCmd) (p : WfPlan),
    (applyAllR cs p).map Prod.fst = applyAll cs p := by
  intro cs
  induction cs with
  | nil => intro p; rfl
  | cons c rest ih =>
    intro p
    have hc := applyCmdR_plan c p
    show ((applyCmdR c p).bind _).map Prod.fst = (applyCmd c p).bind (applyAll rest)
    cases hr : applyCmdR c p with
    | error x => rw [hr] at hc; rw [← hc]; rfl
    | ok qr =>
      rw [hr] at hc
      have hq : applyCmd c p = .ok qr.1 := hc.symm
      rw [hq]
      show ((applyAllR rest qr.1).map _).map Prod.fst = applyAll rest qr.1
      rw [← ih qr.1]
      cases applyAllR rest qr.1 <;> rfl

/-- A stamp on the wire: `D07` / `W37`, the bytes `demoted:` carries, or `null`. -/
def stampJson : Option Field.Stamp → JVal
  | none   => .null
  | some s => .str (Field.renderStamp s)

/-- Minutes on the wire: an integer numerator and a positive denominator, or
`null` for a line with no estimate.  The kernel never divides. -/
def minutesJson : Option Arith.Pos → JVal
  | none   => .null
  | some q => .obj [("num".toList, .num q.val.num), ("den".toList, .num q.val.den)]

/-- One entry, keys in build order. -/
def closeEntryJson (x : CloseEntry) : JVal :=
  .obj [("id".toList, .str x.id), ("grain".toList, .num x.grain.val),
        ("did".toList, .str x.did.name.toList), ("from".toList, .num x.src),
        ("to".toList, .num x.dst), ("stamp".toList, stampJson x.stamp),
        ("min".toList, minutesJson x.minutes)]

/-- The report object: one key per family, `closes` first.  Stage 6's families
are further keys after it. -/
def reportJson (r : Report) : JVal :=
  .obj [("closes".toList, .arr (r.closes.map closeEntryJson))]

def lerrJson : LErr → JVal
  | .dupId i          => jone "dupId" (.str i)
  | .notADemotion i   => jone "notADemotion" (.str i)
  | .ambiguousDemotion i => jone "ambiguousDemotion" (.str i)
  | .duplicatePath pa => jone "duplicatePath" (.str pa)
  | .badLine pa n w   => jone "badLine" (.obj
      [("path".toList, .str pa), ("line".toList, .num n), ("why".toList, .str (toString (repr w)).toList)])
  | .unterminatedComment pa n => jone "unterminatedComment" (.obj
      [("path".toList, .str pa), ("line".toList, .num n)])

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
  show (ranksAscend (splitDoc 0 x.lines).prose &&
      List.all (splitDoc 0 x.lines).prose
        (fun q => !isItemLine q.2 || inComment (splitDoc 0 x.lines).prose q.1)) = true
  rw [Bool.and_eq_true]
  refine ⟨ranksAscend_of_pairwise _ (splitDoc_prose_strict 0 x.lines), ?_⟩
  simp only [List.all_eq_true]
  intro q hq
  cases hc : inComment (splitDoc 0 x.lines).prose q.1 with
  | true => simp
  | false => simp [splitDoc_prose_outside_a_comment_not_item 0 x.lines q hq hc]

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
  let (plan', report) ←
    match applyAllR cmds plan with
    | .ok qr => pure qr
    | .error k => throw (jone "err" (jone "kernel" (.str (kerrName k).toList)))
  let outDocs := plan'.val.docs.zipIdx.map (fun p =>
    JVal.obj
      ([("path".toList, .str p.1.path),
        ("lines".toList, .arr ((renderDocAt plan'.val p.2 p.1).map JVal.str))]
        ++ regionJson p.1.region))
  -- The report is built on this path only: a refusal above carries none.
  return jone "ok" (.obj [("docs".toList, .arr outDocs), ("report".toList, reportJson report)])

/-! ### The response renders the plan once (`@[csimp]`)

`runPlan` asks `renderDocAt` for every document, and each call filters a fresh
render of the whole plan.  `runPlanFast` is the same response with the lines
bucketed once (`linesByDoc`, Fast.lean); `renderDocAt_eq_renderDocFrom` is the
per-document equality, needing only that a `zipIdx` index is in range. -/

def renderDocFrom (ls : List Line) (d : Doc) : List (List Char) :=
  weave (sortByRank d.prose) (sortByRank (ls.map (fun l => (l.site.rank, l.text))))

theorem renderDocAt_eq_renderDocFrom (p : PlanCore) (k : DocIx) (d : Doc) (hk : k < p.docs.length) :
    renderDocAt p k d = renderDocFrom (((linesByDoc p)[k]?).getD []) d := by
  rw [linesByDoc_get p k hk]; rfl

def runPlanFast (plan : WfPlan) (cmds : List ReqCmd) : Except JVal JVal := do
  let (plan', report) ←
    match applyAllR cmds plan with
    | .ok qr => pure qr
    | .error k => throw (jone "err" (jone "kernel" (.str (kerrName k).toList)))
  let byDoc := linesByDoc plan'.val
  let outDocs := plan'.val.docs.zipIdx.map (fun p =>
    JVal.obj
      ([("path".toList, .str p.1.path),
        ("lines".toList, .arr ((renderDocFrom ((byDoc[p.2]?).getD []) p.1).map JVal.str))]
        ++ regionJson p.1.region))
  return jone "ok" (.obj [("docs".toList, .arr outDocs), ("report".toList, reportJson report)])

@[csimp] theorem runPlan_eq_runPlanFast : @runPlan = @runPlanFast := by
  funext plan cmds
  unfold runPlan runPlanFast
  cases applyAllR cmds plan with
  | error k => rfl
  | ok qr =>
    obtain ⟨q, r⟩ := qr
    have : (q.val.docs.zipIdx.map (fun p =>
        JVal.obj
          ([("path".toList, .str p.1.path),
            ("lines".toList, .arr ((renderDocAt q.val p.2 p.1).map JVal.str))]
            ++ regionJson p.1.region))) =
        q.val.docs.zipIdx.map (fun p =>
        JVal.obj
          ([("path".toList, .str p.1.path),
            ("lines".toList, .arr ((renderDocFrom (((linesByDoc q.val)[p.2]?).getD []) p.1).map JVal.str))]
            ++ regionJson p.1.region)) := by
      apply List.map_congr_left
      intro x hx
      rw [renderDocAt_eq_renderDocFrom q.val x.2 x.1 (List.mem_zipIdx' hx).1]
    simp only [pure_bind]
    rw [this]

/-- **The request up to its loaded plan**: the documents, the commands, the clock, the scan and the
loader.  Split out of `run` at stage 5 D10 step L6 so that `runCap` (end of file) loads the plan
once for both the commands and the capacity section; `run` is this, then `runPlan`, unchanged in
behaviour (`run_is_runLoad_then_runPlan`). -/
def runLoad (j : JVal) : Except JVal (WfPlan × List ReqCmd × ReqClock) := do
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
  -- the clock: present-and-malformed is refused here, absent is refused only
  -- by a command that reads it (`parseCmdAt`)
  let clock ←
    match parseClock j with
    | .ok c => pure c
    | .error e => throw (jsonErr e)
  let mut cmds : List ReqCmd := []
  for cj in cmdsJ do
    match parseCmdAt clock cj with
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
  | .ok plan   => return (plan, cmds, clock)

def run (j : JVal) : Except JVal JVal := (runLoad j).bind (fun x => runPlan x.1 x.2.1)

theorem run_is_runLoad_then_runPlan (j : JVal) :
    run j = (runLoad j).bind (fun x => runPlan x.1 x.2.1) := rfl

/-! ## The `tz` and `log` sections (stage 5, D9 track, step B4)

**INSERTED 2026-09-14 (stage 5, D9 track, step B4; design §6.1, §10.1–§10.4, §14.2 row B4).**
The row puts this in "a new section, appended" to this module.  The definitions are here
instead, right after `run`, because `respond` below is the one entry point and Lean defines
before use: `respond` now calls `runWithLog`, which reads these two sections and then `run`.
The theorems about them are appended at the end of the file (section "Stage 5 D9 B4").

**The op is grammar only.**  A request carrying `log` gets every tail line read by
`Log.readLine` (B3): the line warnings by name, a header `[line, tag, id]` for each entry at or
after `want.headersFrom`, and `[line, rendering, display]` for each line of `want.render`.  There
is no checkpoint, reseal or sealed record yet (W1–W3), and no fact (C6), so `ckpt`, `reseal` and
`sealed` must be `null` or absent and `want.facts` `false` or absent; anything else is refused by
the field's name.

**A request without `tz` and `log` is read exactly as before** (`runWithLog_without_a_log_is_run`).
A present `tz` is read and refused if malformed whether or not `log` is there (the request
clock's rule); `log` without `tz` is `tzAbsent`.  Both sections are read before `run`, so their
refusals come first. -/

/-- Why a `tz` section is refused: `{"err":{"log":{"badTz":<why>}}}`. -/
inductive TzWhy
  /-- `tz` is not one object (not an object, or a repeated `tz` key) -/
  | shape
  /-- `key` is absent, repeated or not a string -/
  | key
  /-- `base` is absent, repeated, not a string or not `±HH:MM:SS` -/
  | base
  /-- `then` is absent, repeated or not an array -/
  | then_
  /-- an element of `then` is not a pair of strings -/
  | transition
  /-- a transition's instant is not a stamp at UTC in whole seconds -/
  | instant
  /-- a transition's offset is not `±HH:MM:SS` -/
  | offset
  /-- `key` is longer than 128 characters (`Cal.TzTable.wf`) -/
  | keyTooLong
  /-- more than 4,096 transitions (`Cal.TzTable.wf`) -/
  | tooManyTransitions
  /-- the transitions are not strictly increasing (`Cal.mkTz?` refuses) -/
  | unsorted
deriving DecidableEq, Repr

def TzWhy.name : TzWhy → String
  | .shape => "shape" | .key => "key" | .base => "base" | .then_ => "then"
  | .transition => "transition" | .instant => "instant" | .offset => "offset"
  | .keyTooLong => "keyTooLong" | .tooManyTransitions => "tooManyTransitions"
  | .unsorted => "unsorted"

/-- The `log` section's fields, as `badLogReq` names them. -/
inductive LogField
  | log | ckpt | from_ | lines | terminated | reseal | want | facts | headersFrom | render | sealed
deriving DecidableEq, Repr

def LogField.name : LogField → String
  | .log => "log" | .ckpt => "ckpt" | .from_ => "from" | .lines => "lines"
  | .terminated => "terminated" | .reseal => "reseal" | .want => "want" | .facts => "facts"
  | .headersFrom => "headersFrom" | .render => "render" | .sealed => "sealed"

/-- **The `log` op's refusals at B4** (design §10.3; W3 adds the checkpoint's).  None is a line of
the log: a line never refuses a request, it is a warning. -/
inductive LogRefusal
  /-- `log` without `tz` -/
  | tzAbsent
  | badTz (why : TzWhy)
  /-- more than 32,768 lines in one call -/
  | tooManyLines
  | badLogReq (field : LogField)
  /-- a `want.render` line outside `[from, from + lines − 1]` -/
  | renderNotInTail (line : Nat)
deriving DecidableEq, Repr

/-- Keys in build order: `{"err":{"log":…}}`. -/
def LogRefusal.json : LogRefusal → JVal
  | .tzAbsent => jone "err" (jone "log" (.str "tzAbsent".toList))
  | .badTz w => jone "err" (jone "log" (jone "badTz" (.str w.name.toList)))
  | .tooManyLines => jone "err" (jone "log" (.str "tooManyLines".toList))
  | .badLogReq f => jone "err" (jone "log" (jone "badLogReq" (.str f.name.toList)))
  | .renderNotInTail n => jone "err" (jone "log" (jone "renderNotInTail" (jone "line" (.num n))))

/-! ### `tz`: the zone table Rust probes (design §6.1), read by the kernel's own readers -/

/-- Two decimal digits. -/
def digits2 (a b : Char) : Option Nat :=
  match charDigit a, charDigit b with
  | some x, some y => some (10 * x + y)
  | _, _ => none

/-- **A table offset, `±HH:MM:SS`**, the one spelling `tz_table.rs` writes: nine characters,
`+` or `-`, hours ≤ 23, minutes and seconds ≤ 59, and `+` at zero (so UTC has one spelling).
The smart constructor is `Cal.mkOffset?`. -/
def readTzOffset : List Char → Option Cal.VOffset
  | [sg, h1, h2, ':', m1, m2, ':', s1, s2] =>
    match (if sg = '+' then some false else if sg = '-' then some true else none),
        digits2 h1 h2, digits2 m1 m2, digits2 s1 s2 with
    | some west, some h, some m, some s =>
      if h ≤ 23 ∧ m ≤ 59 ∧ s ≤ 59 ∧ (west = false ∨ 0 < h * 3600 + m * 60 + s) then
        Cal.mkOffset? west (h * 3600 + m * 60 + s)
      else none
    | _, _, _, _ => none
  | _ => none

/-- **A transition's instant**: a stamp `LogStamp.parseStamp` reads (B2), at UTC, in whole
seconds.  `tz_table.rs` writes `YYYY-MM-DDTHH:MM:SSZ`. -/
def readTzInstant (s : List Char) : Option Cal.Instant :=
  match LogStamp.parseStamp s with
  | .ok (i, o) => if o.val = Cal.Offset.utc ∧ i.val.ns = 0 then some i.val else none
  | .error _ => none

def readTransition : JVal → Except TzWhy (Cal.Instant × Cal.Offset)
  | .arr [.str a, .str b] =>
    match readTzInstant a, readTzOffset b with
    | some i, some o => .ok (i, o.val)
    | none, _ => .error .instant
    | some _, none => .error .offset
  | _ => .error .transition

/-- One step of reading `then`, reversed; a `foldl` (D9-21), run only below the 4,096 bound. -/
def transStep (acc : Except TzWhy (List (Cal.Instant × Cal.Offset))) (x : JVal) :
    Except TzWhy (List (Cal.Instant × Cal.Offset)) :=
  match acc, readTransition x with
  | .ok ys, .ok p => .ok (p :: ys)
  | .error e, _ => .error e
  | .ok _, .error e => .error e

/-- **The `tz` section**: `{"key": s, "base": "±HH:MM:SS", "then": [[instant, offset], …]}`.  The
bounds are checked before `then`'s elements are read, and the table is built only through
`Cal.mkTz?` (R10), whose one remaining refusal after the readers is an unsorted table. -/
def readTz (j : JVal) : Except TzWhy Cal.Tz :=
  match j with
  | .obj _ =>
    match jget j "key" with
    | .ok (some (.str key)) =>
      match jget j "base" with
      | .ok (some (.str b)) =>
        match readTzOffset b with
        | some base =>
          match jget j "then" with
          | .ok (some (.arr xs)) =>
            if 128 < key.length then .error .keyTooLong
            else if 4096 < xs.length then .error .tooManyTransitions
            else
              match xs.foldl transStep (.ok []) with
              | .error e => .error e
              | .ok rev =>
                match Cal.mkTz? ⟨key, base.val, rev.reverse⟩ with
                | some z => .ok z
                | none => .error .unsorted
          | _ => .error .then_
        | none => .error .base
      | _ => .error .base
    | _ => .error .key
  | _ => .error .shape

/-! ### `log`: the request (design §10.1) and its smart constructor `mkLogReq?` (§10.4) -/

/-- What the B4 op reads of a `log` section. -/
structure LogReq where
  /-- the physical line number of `lines[0]` -/
  from_ : Nat
  /-- each line's characters, or `none` for a line the host found not to be UTF-8 -/
  lines : List (Option (List Char))
  /-- whether the last line had its `\n` (W3 never folds an unterminated one; B4 folds nothing) -/
  terminated : Bool
  headersFrom : Option Nat
  render : List Nat
  /-- `want.facts` (stage 5 D9 C1): the tail's replay facts; at C1, its cancelled line set.  Last, so
  the five fields before it keep their places. -/
  facts : Bool
deriving DecidableEq, Repr

/-- Line numbers on the wire are below `2^40` (§10.4). -/
def logLineBound : Nat := 1099511627776
/-- Lines per call (§10.4; Rust also caps the bytes). -/
def maxLogLines : Nat := 32768
/-- Lines per `want.render` (§10.4). -/
def maxRenderLines : Nat := 4096

/-- **The first bound a request breaks, by name** (§10.4's rows for `from`, lines per call,
`headersFrom` and `render`).  A `render` line must lie in the tail, which also puts it below
`2^40 + 32,768`. -/
def LogReq.fault (r : LogReq) : Option LogRefusal :=
  if r.from_ = 0 ∨ logLineBound ≤ r.from_ then some (.badLogReq .from_)
  else if maxLogLines < r.lines.length then some .tooManyLines
  else if r.headersFrom.any (fun h => decide (logLineBound ≤ h)) then
    some (.badLogReq .headersFrom)
  else if maxRenderLines < r.render.length then some (.badLogReq .render)
  else
    match r.render.find? (fun n => n < r.from_ || r.from_ + r.lines.length ≤ n) with
    | some n => some (.renderNotInTail n)
    | none => if r.facts && r.from_ != 1 then some (.badLogReq .facts) else none

def LogReq.wf (r : LogReq) : Bool := r.fault.isNone

abbrev VLogReq := { r : LogReq // r.wf = true }

/-- **The only constructor the decoder uses (R10).** -/
def mkLogReq? (r : LogReq) : Except LogRefusal VLogReq :=
  match h : r.fault with
  | some f => .error f
  | none => .ok ⟨r, by simp [LogReq.wf, h]⟩

/-- Absent or `null`: what B4 accepts for `ckpt`, `reseal` and `sealed`. -/
def nullOrAbsent (j : JVal) (k : String) : Bool :=
  match jget j k with
  | .ok none => true
  | .ok (some .null) => true
  | _ => false

/-- One step of reading `lines`, reversed; a `foldl` (D9-21), run only below the line bound. -/
def lineStep (acc : Except LogRefusal (List (Option (List Char)))) (x : JVal) :
    Except LogRefusal (List (Option (List Char))) :=
  match acc, x with
  | .ok ys, .str s => .ok (some s :: ys)
  | .ok ys, .null => .ok (none :: ys)
  | .ok _, _ => .error (.badLogReq .lines)
  | .error e, _ => .error e

/-- One step of reading `want.render`, reversed; a `foldl`, run only below its bound. -/
def renderStep (acc : Except LogRefusal (List Nat)) (x : JVal) : Except LogRefusal (List Nat) :=
  match acc, x with
  | .ok ys, .num n => .ok (n :: ys)
  | .ok _, _ => .error (.badLogReq .render)
  | .error e, _ => .error e

/-- `want`: `facts` absent or a boolean (stage 5 D9 C1; B4 accepted only `false`), `headersFrom`
absent, `null` or a number, `render` absent or an array of numbers.  An absent `want` wants
nothing. -/
def readWant (w : Option JVal) : Except LogRefusal (Bool × Option Nat × List Nat) :=
  match w with
  | none => .ok (false, none, [])
  | some w@(.obj _) =>
    match jget w "facts" with
    | .ok none => readHeaders false w
    | .ok (some (.bool fa)) => readHeaders fa w
    | _ => .error (.badLogReq .facts)
  | some _ => .error (.badLogReq .want)
where
  readHeaders (fa : Bool) (w : JVal) : Except LogRefusal (Bool × Option Nat × List Nat) :=
    match jget w "headersFrom" with
    | .ok none | .ok (some .null) =>
      (readRender w).map (fun rs => (fa, none, rs))
    | .ok (some (.num h)) => (readRender w).map (fun rs => (fa, some h, rs))
    | _ => .error (.badLogReq .headersFrom)
  readRender (w : JVal) : Except LogRefusal (List Nat) :=
    match jget w "render" with
    | .ok none => .ok []
    | .ok (some (.arr rs)) =>
      if maxRenderLines < rs.length then .error (.badLogReq .render)
      else (rs.foldl renderStep (.ok [])).map List.reverse
    | _ => .error (.badLogReq .render)

/-- **The `log` section**, field by field, then `mkLogReq?`.  `lines` is measured before its
elements are read. -/
def readLogReq (j : JVal) : Except LogRefusal VLogReq :=
  match j with
  | .obj _ =>
    if !nullOrAbsent j "ckpt" then .error (.badLogReq .ckpt) else
    match jget j "from" with
    | .ok (some (.num from_)) =>
      match jget j "lines" with
      | .ok (some (.arr xs)) =>
        if maxLogLines < xs.length then .error .tooManyLines else
        match xs.foldl lineStep (.ok []) with
        | .error e => .error e
        | .ok rev =>
          match jget j "terminated" with
          | .ok (some (.bool term)) =>
            if !nullOrAbsent j "reseal" then .error (.badLogReq .reseal)
            else if !nullOrAbsent j "sealed" then .error (.badLogReq .sealed)
            else
              match jget j "want" with
              | .ok w =>
                match readWant w with
                | .ok (fa, hf, rs) => mkLogReq? ⟨from_, rev.reverse, term, hf, rs, fa⟩
                | .error e => .error e
              | .error _ => .error (.badLogReq .want)
          | _ => .error (.badLogReq .terminated)
      | _ => .error (.badLogReq .lines)
    | _ => .error (.badLogReq .from_)
  | _ => .error (.badLogReq .log)

/-! ### `log`: the answer (design §10.2, B4's part) -/

def stampErrName : LogStamp.StampErr → String
  | .tooShort => "tooShort" | .badDate => "badDate" | .badSeparator => "badSeparator"
  | .badTime => "badTime" | .badFraction => "badFraction" | .badOffset => "badOffset"
  | .tooLong => "tooLong" | .beforeOrigin => "beforeOrigin" | .pastYear9999 => "pastYear9999"

/-- A line warning: `{"line":n,"w":name}`, with `key` for a field and `why` for a parse or a
stamp. -/
def lwarnJson (n : Nat) (w : Log.LWarn) : JVal :=
  let at_ (name : String) (extra : List (List Char × JVal)) : JVal :=
    .obj ([("line".toList, .num n), ("w".toList, .str name.toList)] ++ extra)
  match w with
  | .invalidUtf8 => at_ "invalidUtf8" []
  | .lineTooLong => at_ "lineTooLong" []
  | .lineTooDeep => at_ "lineTooDeep" []
  | .notJson e => at_ "notJson" [("why".toList, .str (jerrText e).toList)]
  | .numberOutOfRange => at_ "numberOutOfRange" []
  | .notAnObject => at_ "notAnObject" []
  | .noT => at_ "noT" []
  | .tNotString => at_ "tNotString" []
  | .badT e => at_ "badT" [("why".toList, .str (stampErrName e).toList)]
  | .duplicateT => at_ "duplicateT" []
  | .noEv => at_ "noEv" []
  | .evNotString => at_ "evNotString" []
  | .missingField k => at_ "missingField" [("key".toList, .str k)]
  | .badField k => at_ "badField" [("key".toList, .str k)]

/-- A header at B4: `[line, tag, id]` (`Event::name`, `Event::primary_id`).  C6 adds the day,
the cancelled flag and the display. -/
def headerJson (e : Log.Entry) : JVal :=
  .arr [.num e.line, .str e.ev.tag,
    match e.ev.primaryId with
    | some i => .str i
    | none => .null]

/-- A rendering: `[line, renderLine, displayStamp]`, or `[line, null, null]` for a line that is
blank or a warning. -/
def renderJson (n : Nat) : Option Log.Verdict → JVal
  | some (.entry e) =>
    .arr [.num n, .str (Log.renderLine e), .str (LogStamp.displayStamp e.t e.off)]
  | _ => .arr [.num n, .null, .null]

def readStep (acc : List Log.Verdict × Nat) (seg : Option (List Char)) : List Log.Verdict × Nat :=
  (Log.readLine acc.2 seg :: acc.1, acc.2 + 1)

/-- **Every line of the tail, read by `Log.readLine` at its physical number.**  A `foldl`
(`logVerdicts_eq`). -/
def logVerdicts (r : LogReq) : List Log.Verdict := (r.lines.foldl readStep ([], r.from_)).1.reverse

def warningOf : Log.Verdict → Option JVal
  | .warn n w => some (lwarnJson n w)
  | _ => none

def headerOf (hf : Nat) : Log.Verdict → Option JVal
  | .entry e => if hf ≤ e.line then some (headerJson e) else none
  | _ => none

def entryOf : Log.Verdict → Option Log.Entry
  | .entry e => some e
  | _ => none

/-- **The tail's facts** (design §10.2's `facts`, stage 5 D9 C1): at C1 the cancelled line set, the
lines of the entries the undo mask cancels (`Replay.cancelledLines`, compiled as its fast twin), in
file order.  C6 replaces this with the whole view. -/
def factsJson (es : List Log.Entry) : JVal :=
  .obj [("cancelled".toList, .arr ((Replay.cancelledLines es).map JVal.num))]

/-- **The `log` answer**: `lines` (the last physical line seen), `warnings`, `headers`, `render`,
keys in build order.  `render` looks its lines up in an array. -/
def logAnswer (r : VLogReq) : JVal :=
  let vs := logVerdicts r.val
  let arr := vs.toArray
  .obj [("lines".toList, .num (r.val.from_ + r.val.lines.length - 1)),
        ("warnings".toList, .arr (vs.filterMap warningOf)),
        ("facts".toList, if r.val.facts then factsJson (vs.filterMap entryOf) else .null),
        ("headers".toList, .arr (match r.val.headersFrom with
          | none => []
          | some hf => vs.filterMap (headerOf hf))),
        ("render".toList, .arr (r.val.render.map (fun n => renderJson n arr[n - r.val.from_]?)))]

/-- **The two sections of a request.**  Not an object: nothing (`run` refuses it as before).
`tz` is read when present; `log` needs it. -/
def readLogSection (j : JVal) : Except JVal (Option VLogReq) :=
  match j with
  | .obj _ =>
    match jget j "tz" with
    | .error _ => .error (LogRefusal.badTz .shape).json
    | .ok tz =>
      match tz.map readTz with
      | some (.error w) => .error (LogRefusal.badTz w).json
      | _ =>
        match jget j "log" with
        | .ok none => .ok none
        | .ok (some l) =>
          if tz.isNone then .error LogRefusal.tzAbsent.json
          else
            match readLogReq l with
            | .ok r => .ok (some r)
            | .error e => .error e.json
        | .error _ => .error (LogRefusal.badLogReq .log).json
  | _ => .ok none

/-- The `log` answer after `report` in the `ok` object. -/
def withLog (a : JVal) : JVal → JVal
  | .obj [(k, .obj kvs)] => .obj [(k, .obj (kvs ++ [("log".toList, a)]))]
  | r => r

/-- **The request, with its `log` section.**  Without one it is `run` (definitionally). -/
def runWithLog (j : JVal) : Except JVal JVal :=
  match readLogSection j with
  | .error e => .error e
  | .ok none => run j
  | .ok (some r) => (run j).map (withLog (logAnswer r))


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
comes back byte for byte.

**Since D6 the month document carries `^O2`**, the outcome both lines name with
`@O2` — §4.3's own month file, whose `# Outcomes` stands above its `# Demoted`.
Without it the request is refused `itemCheck: danglingParent` (README gap 22,
closed), as every tree whose parent link names an id it does not carry is; so
the entity list has two members, the outcome and the pair. -/

def specWeekDoc : ReqDoc :=
  ⟨"week/2026-W37.md", some ⟨week, 35⟩,
    ["# Milestones".toList,
     "- [ ] 4 6b Rollback path passes tests   @O2 ^m2".toList]⟩

def specMonthDoc : ReqDoc :=
  ⟨"month/2026-09.md", some ⟨month, 8⟩,
    ["# Outcomes".toList,
     "- [ ] 4 !1 Soundcode: end-to-end demo runs             ^O2".toList,
     "# Demoted".toList,
     "- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2".toList]⟩

def specDemotionRequest : List ReqDoc := [specWeekDoc, specMonthDoc]

/-- The entity the loader builds for `^m2` from that request, if it builds exactly
two — `^m2` and its parent `^O2`. -/
def specPairEntity : Option Entity :=
  match buildEntities (placementsOf 0 specDemotionRequest) with
  | .ok items =>
    if items.length = 2 then (items.find? (fun q => q.1 == "m2".toList)).map Prod.snd else none
  | .error _ => none

set_option maxRecDepth 40000 in
/-- **The two lines become one entity, and it has a tombstone.**  Not two
entities, not one line dropped: the pair is read as the demotion it is (the
request's second entity is the outcome `^O2`). -/
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
        = ["# Outcomes".toList,
           "- [ ] 4 !1 Soundcode: end-to-end demo runs             ^O2".toList,
           "# Demoted".toList,
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

/-- On a loaded plan, no placement the walk built sits inside a comment of its
document — `splitDoc_items_outside_comments`, read through `mkDoc`. -/
theorem commentAt_loadCore_placement (docs : List ReqDoc) (items : List (Id × Entity))
    {q : Placement} (hq : q ∈ placementsOf 0 docs) :
    commentAt (loadCore docs items) ⟨q.doc, q.rank⟩ = false := by
  obtain ⟨j, d, hd, hqj⟩ := (mem_placementsOf q 0 docs).1 hq
  obtain ⟨it, hit, hqe⟩ := mem_placementsOfDoc.1 hqj
  rw [hqe, Nat.zero_add]
  suffices h : (docs.map mkDoc)[j]? = some (mkDoc d) by
    show (match (docs.map mkDoc)[j]? with
      | none => false
      | some dd => inComment dd.prose it.1) = false
    rw [h]
    exact splitDoc_items_outside_comments 0 d.lines it hit
  rw [List.getElem?_map, hd]
  rfl

/-- An entity `buildEntity` accepts has neither of its sites inside a comment on
the loaded plan — the same two arms as `entityInRange_loadEntity`. -/
theorem entityUncommented_loadEntity {docs : List ReqDoc} {items : List (Id × Entity)}
    {qs : List Placement} {i : Id} {e : Entity}
    (hsub : ∀ q ∈ qs, q ∈ placementsOf 0 docs)
    (h : buildEntity i qs = .ok e) :
    commentAt (loadCore docs items) e.val.live = false ∧
      (∀ r, e.val.archiveSite = some r → commentAt (loadCore docs items) r = false) := by
  match qs with
  | [] => simp [buildEntity] at h
  | [q] =>
      have h' : e = loneEntity q := by
        have this : Except.ok (loneEntity q) = (.ok e : Except LErr Entity) := h
        injection this with this
        exact this.symm
      rw [h']
      refine ⟨commentAt_loadCore_placement docs items (hsub q (by simp)), fun r hr => ?_⟩
      have hnone : (loneEntity q).val.archiveSite = none := rfl
      rw [hnone] at hr
      cases hr
  | [a, b] =>
      have h' : pairedEntity i a b = .ok e := h
      obtain ⟨arch, live, hor, _hcond, hllive, harch, _hline, _hag, _hglive, _hgarch⟩ :=
        paired_placement_renders_back i a b e h'
      obtain ⟨har, hal⟩ := placement_bounds_pair (hsub a (by simp)) (hsub b (by simp))
        (orientPair_cases hor).1
      refine ⟨?_, fun r hr => ?_⟩
      · rw [hllive]
        exact commentAt_loadCore_placement docs items hal
      · rw [Core.archiveSite_some harch] at hr
        simp only [Option.some.injEq] at hr
        rw [← hr]
        exact commentAt_loadCore_placement docs items har
  | _ :: _ :: _ :: _ => simp [buildEntity] at h

/-- **The loader places no item inside a comment** — the over-bite guard for the
comment conjunct of `placementSectionWf`: the check `loadPlan` runs can refuse
a *command's* post-state that ranks a line into a comment, and is bound to pass
every placement the loader itself read (a line inside a comment was never read
as an item in the first place). -/
theorem the_loader_places_no_item_in_a_comment (docs : List ReqDoc)
    (items : List (Id × Entity)) (h : buildEntities (placementsOf 0 docs) = .ok items)
    (i : Id) (e : Entity) (hget : (loadStore items).get i = some e) :
    commentAt (loadCore docs items) e.val.live = false ∧
      (∀ r, e.val.archiveSite = some r → commentAt (loadCore docs items) r = false) :=
  entityUncommented_loadEntity (fun q hq => (List.mem_filter.1 hq).1)
    ((buildEntities_spec (placementsOf 0 docs) items h).2 (i, e)
      (loadStore_get_some items i e hget))

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
`the_response_call_emits_parses_back` is about the exported function's bytes.  Since stage 5 D9
B4 it runs `runWithLog`, which is `run` for a request without a `log` section
(`runWithLog_without_a_log_is_run`). -/
def respond (input : List Char) : JVal :=
  match jparse input with
  | .error e => jsonErr s!"bad json: {jerrText e}"
  | .ok j =>
    match runWithLog j with
    | .error e => e
    | .ok r    => r

/-- Total: every path returns a `String`.  No `panic!`, no `!`, no `partial`.
No `Lean.Json` either: `jparse` in, `jemit` out (J5). -/
def call (input : String) : String := String.ofList (jemit (respond input.toList))

-- `@[export tm_kernel_call] def callExport` moved to the end of this file at stage 5 D10 step
-- L6: the FFI runs `callCap`, which is `call` on every request without `capacity`
-- (`callExport_without_capacity_is_call`).

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
    -- the two close commands (stage 4 step 5): a close moves `^m1` only out of
    -- a file of its own grain's kind — the month file, so a month close — and
    -- only into a month file, or, for a wall, the week, or, past due (D7), the
    -- backlog; `^m1` is no wall, and document 0 is a week file
    have hnoclose : ∀ (g : Grain) (now : Day) (x : FoldFx),
        stepSkel g now q.val x e1.val.skel ≠ e.val.skel := by
      intro g now x heq
      have hd0 : (stepSkel g now q.val x e1.val.skel).doc = 0 := by
        rw [heq]; exact congrArg Site.doc hml
      have hd1 : e1.val.skel.doc = 1 := congrArg Site.doc he1live
      have hk := stepSkel_doc_kinds g now q.val x e1.val.skel (by rw [hd0, hd1]; decide)
      have hk0 : docKindAt q.val 0 = .week := by
        rw [hshape]; exact (by decide : docKindAt undoWitnessPlan.val 0 = .week)
      have hk1 : docKindAt q.val 1 = .month := by
        rw [hshape]; exact (by decide : docKindAt undoWitnessPlan.val 1 = .month)
      rw [hd0, hk0, hd1, hk1] at hk
      have hg : g = month := by
        match g, hk.1 with
        | ⟨2, _⟩, _ => rfl
      subst hg
      rcases hk.2 with hc | ⟨⟨b, hw⟩, _⟩ | ⟨_, hc⟩
      · exact absurd hc (by decide)
      · have hshp := (by decide : (undoWitnessPlan.val.store.get "m1".toList).map
          (fun x : Entity => match Field.viewShape x.val.line with
            | .interval _ _ => true | _ => false) = some false)
        rw [hgetE] at hshp
        have hl : e1.val.line = e.val.line := by rw [he1v]
        simp only [Skel.wallAhead, Core.skel, hl, Option.map_some, Option.some.injEq] at hw hshp
        split at hw
        · rename_i hi; rw [hi] at hshp; simp at hshp
        · simp at hw
      · exact absurd hc (by decide)
    -- nine shapes, one refuted observable each
    cases hcmd : inv (.move "m1".toList 1) with
    | close g now bm =>
      rw [hcmd] at hcon
      exact hnoclose g now _ (close_skel hcon hq1 hgetE).symm
    | autoClose now bm =>
      rw [hcmd] at hcon
      obtain ⟨g, hg⟩ := autoClose_takes_each_line_at_most_once hcon hq1 hgetE
      exact hnoclose g now _ hg.symm
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
      have h := hback i' _ (nameEditFault_ok hcon)
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
      have h := hback i' _ (nameEditFault_ok hcon)
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
        simp only [applyCmd, hrd'] at hcon
        -- neither witness file has a `# Demoted`, so the verb lands at the end
        -- of the file (gap 20's fallback) and is one `mapAt`
        have hdocs : q.val.docs = undoWitnessPlan.val.docs := by rw [hshape]
        have hnone : demoteSpot q.val dd.ix = none := by
          have hk : dd.ix < 2 := by
            have := dd.ok; rw [hdocs] at this; exact this
          have hall : ∀ k, k < 2 → demoteSpot undoWitnessPlan.val k = none := by decide
          rw [← hall dd.ix hk]
          unfold demoteSpot landingSpot
          rw [hdocs]
        rw [hnone] at hcon
        have h := hback i' _ (guardStray_ok hcon).1
        have hev := refile_roundtrips _ _ _ _ h
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
  show nameEditFault p i v (p.mapAt i (editE v)) = .error .tabbedLine
  have hm : p.mapAt i (editE v) = .error .tabbedLine := by
    unfold WfPlan.mapAt
    split
    · rename_i hn; rw [hget] at hn; simp at hn
    · rename_i a hget'
      rw [hget] at hget'
      injection hget' with hget'
      subst hget'
      rw [editE_refuses_a_tabbed_line v _ htab]
  rw [hm]; rfl

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
  refine ⟨q, ?_, hqi⟩
  show nameEditFault p i v (p.mapAt i (editE v)) = .ok q
  rw [hq]; rfl

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
that is no key, the one key kept off the wire (`demoted`, README gap 40), and two values the field
grammars refuse — `ci:7` is the `Fin 6` smart constructor biting (R10), and
`est=3d` is `NdDur` refusing a day-carrying estimate. -/
theorem parseCmd_rejects_edit_variants :
    parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "size".toList), ("value".toList, .str "3".toList)]) = .error "unknownKey size" ∧
    parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "demoted".toList), ("value".toList, .str "W37".toList)]) = .error "keyNotWired demoted" ∧
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

set_option maxRecDepth 8000 in
/-- **The response shapes, byte for byte, in build order.**  The free-text
`err`, a `kernel` refusal, and an `ok` document — `path`, then `lines`, then the
region's `grain` and `ix` — with a quote in the line so the escaping is on the
path being pinned.  Small by design (the Json.lean memory rule): emission is
evaluated, never a parser run.  Extended at stage 5 D9 B4 (design §10.2): three `log` refusals,
a line warning, and a `log` answer after `report`. -/
theorem the_response_shapes_emit_in_build_order :
    jemit (jsonErr "unknown op fly") = "{\"err\":\"unknown op fly\"}".toList ∧
    jemit (jone "err" (jone "kernel" (.str "noSuchId".toList)))
      = "{\"err\":{\"kernel\":\"noSuchId\"}}".toList ∧
    jemit (jone "ok" (jone "docs" (.arr [.obj ([("path".toList, .str "w.md".toList),
        ("lines".toList, .arr [.str "- [ ] a \"q\" ^x1".toList])] ++ regionJson (some ⟨1, 35⟩))])))
      = "{\"ok\":{\"docs\":[{\"path\":\"w.md\",\"lines\":[\"- [ ] a \\\"q\\\" ^x1\"],\"grain\":1,\"ix\":35}]}}".toList ∧
    -- stage 5 D9 B4: the `log` refusals, and the `log` answer after `report`
    jemit LogRefusal.tzAbsent.json = "{\"err\":{\"log\":\"tzAbsent\"}}".toList ∧
    jemit (LogRefusal.badTz .unsorted).json = "{\"err\":{\"log\":{\"badTz\":\"unsorted\"}}}".toList ∧
    jemit (LogRefusal.renderNotInTail 45101).json
      = "{\"err\":{\"log\":{\"renderNotInTail\":{\"line\":45101}}}}".toList ∧
    -- W-2 repair: the `log` answer after `report` is pinned in three pieces, none over design
    -- §14.0.4's 90 characters (B4 had one 142-character literal): the envelope with `log` last
    -- (`withLog_jone`), the answer's value with its keys in order, and the warning's bytes.
    jemit (withLog .null (jone "ok" (.obj [("docs".toList, .arr []), ("report".toList, reportJson Report.empty)])))
      = "{\"ok\":{\"docs\":[],\"report\":{\"closes\":[]},\"log\":null}}".toList ∧
    logAnswer ⟨⟨17, [none], true, some 17, [17], false⟩, by decide⟩
      = .obj [("lines".toList, .num 17), ("warnings".toList, .arr [lwarnJson 17 .invalidUtf8]),
          ("facts".toList, .null), ("headers".toList, .arr []), ("render".toList, .arr [.arr [.num 17, .null, .null]])] ∧
    jemit (lwarnJson 17 .invalidUtf8) = "{\"line\":17,\"w\":\"invalidUtf8\"}".toList ∧
    jemit (lwarnJson 17 (.missingField ['s', 'l', 'e', 'p', 't', '_', 'm', 'i', 'n']))
      = "{\"line\":17,\"w\":\"missingField\",\"key\":\"slept_min\"}".toList := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The `log` answer goes last in the `ok` object** (W-2 repair), for every answer and every key
list: what composes `the_response_shapes_emit_in_build_order`'s three `log`-answer conjuncts into
the response's bytes, since `jemit` is structural. -/
theorem withLog_jone (a : JVal) (k : String) (kvs : List (List Char × JVal)) :
    withLog a (jone k (.obj kvs)) = jone k (.obj (kvs ++ [("log".toList, a)])) := rfl

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
and this is its instance at the code `callExport` ran until stage 5 D10 step L6 (since
then `callExport` runs `callCap`: `the_exported_call_emits_parses_back`, and
`callExport_without_capacity_is_call` carries every `call` theorem to it).  What it does not say,
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
  have hrun : runWithLog demoRequest = .error demoResponse := rfl
  unfold call respond
  rw [String.toList_ofList, the_real_request_bytes_round_trip.2]
  simp only [hrun]
  rw [the_real_response_bytes_round_trip.1]

/-! ## A comment is prose — the witnesses (stage 3, 2026-09-12)

The defect, driven out of the shipped binary: the starter templates' guidance
comments held example item lines, so a bare `tm init` tree refused every
kernel-backed verb (`itemCheck: danglingDep` on ids that exist only inside
`<!-- -->`).  The reading is `commentAfter`'s (Plan.lean).  The general theorems
are `splitDocC_reads_comments`, `the_loader_places_no_item_in_a_comment`,
`scanLines_prose_outside_a_comment` and `scanLines_accepts_only_closed_comments`;
these are the small decided instances, each probed under an 8 GB cap first.

The witness document holds, inside one comment, an example item carrying the
**same id** as the live item below it, a broken item shape, and a `# Demoted`
heading — a month-only section in a week file.  Each of the three would refuse
the file if it were read (`dupId`, `badLine`, `sectionDiscipline`). -/

def commentedWeekDoc : ReqDoc :=
  ⟨"week/2026-W37.md", some ⟨week, 35⟩,
    ["# Tasks".toList, "<!-- e.g.".toList, "- [ ] 3 1b Example ^m1".toList,
     "- [Z] broken".toList, "# Demoted".toList, "-->".toList,
     "- [ ] 5 6b Finish the report ^m1".toList]⟩

def commentedRequest : List ReqDoc :=
  [commentedWeekDoc, ⟨"month/2026-09.md", some ⟨month, 8⟩, ["# Outcomes".toList]⟩]

/-- **The behaviour change, separated.**  The commented example line *is* an item
line — the comment-blind reader this replaces took it as one — and the
splitter now files it, the broken shape and the heading as prose: lines 0–5 are
prose and line 6 is the one item. -/
theorem a_commented_item_line_loads_as_prose :
    isItemLine "- [ ] 3 1b Example ^m1".toList = true ∧
      (splitDoc 0 commentedWeekDoc.lines).items.map Prod.fst = [6] ∧
      (splitDoc 0 commentedWeekDoc.lines).prose.map Prod.fst = [0, 1, 2, 3, 4, 5] := by
  decide

/-- And the whole boundary accepts it: the scan (no `badLine` for the broken
example) and the loader (no `dupId` for the repeated `^m1`, no
`sectionDiscipline` for the commented `# Demoted`). -/
theorem the_commented_request_loads :
    scanLines "week/2026-W37.md".toList 0 commentedWeekDoc.lines = .ok () ∧
      loadsOk commentedRequest = true :=
  ⟨rfl, by decide⟩

/-- The round trip is unaffected: the loaded document comes back byte for byte,
comment included. -/
theorem the_commented_request_round_trips (p : WfPlan) (h : loadPlan commentedRequest = .ok p) :
    renderDocAt p.val 0 (mkDoc commentedWeekDoc) = commentedWeekDoc.lines :=
  (the_kernel_reads_back_what_it_writes commentedRequest p h 0 commentedWeekDoc rfl).2

/-- A heading inside a comment is not a section: the section of the live item is
`# Tasks`, not the commented `# Demoted`. -/
theorem a_commented_heading_is_no_section :
    lastHeadingBefore (mkDoc commentedWeekDoc) 6 = some (0, "# Tasks".toList) := by
  decide

/-- **The over-bite guard, decided.**  The same example and live item with the
comment markers gone are two items again, and the loader refuses the repeated
id; and an inline `<!--` that does not start its line opens nothing, so the
item after it is still an item. -/
def uncommentedRequest : List ReqDoc :=
  [⟨"week/2026-W37.md", some ⟨week, 35⟩,
    ["# Tasks".toList, "- [ ] 3 1b Example ^m1".toList,
     "- [ ] 5 6b Finish the report ^m1".toList]⟩,
   ⟨"month/2026-09.md", some ⟨month, 8⟩, ["# Outcomes".toList]⟩]

theorem an_item_line_outside_a_comment_is_still_an_item :
    loadsOk uncommentedRequest = false ∧
      (splitDoc 0 ["see <!-- inline".toList, "- [ ] 2 30m Live ^t3".toList]).items.length = 1 := by
  decide

/-- **The unterminated-comment decision, witnessed**: a comment open at the end
of a file is refused by name, at its opener's line, and the item line after the
opener is not read. -/
theorem an_unterminated_comment_is_refused :
    scanLines "week/2026-W37.md".toList 0
        ["# Tasks".toList, "<!--".toList, "- [ ] 3 x ^t1".toList] =
      .error (.unterminatedComment "week/2026-W37.md".toList 1) :=
  rfl


/-! ## Gap 40's bridges on the wire (stage 3, step 5)

Eight more keys reach `parseCmd` — `due`, `at`, `win`, `every`, `on-event`,
`loc`, `waiting`, `after` — each through its Line.lean bridge (`parseDate_dayWf`
and its heirs) and `guardWf`, so the table's refusals are the loader parser's
own (Cmd.lean's `editValOf_*_refuses_only_*`).  `demoted` stays excluded by
policy (`keyNotWired demoted`, Negative.lean CHEAT 45).  `after` additionally
meets the plan tier: its post-state can dangle or cycle, and those refusals are
named (`danglingDep`, `depCycle`) instead of `mapAt`'s `badHorizon`. -/

/-- §5.7 at the parse tier, one named refusal per bridged key — a value the
key's grammar rejects (Feb 30, an end before its start, hour 25, a zero period,
a name with a space, an unpadded date, an empty id), `loc:`'s word bound (a
space), and `at:`'s one false bridge (the year-9999 rollover the loader
reads). -/
theorem parseCmd_refuses_the_bridged_keys_bad_values :
    parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "due".toList), ("value".toList, .str "2026-02-30".toList)]) = .error "badValue due" ∧
    parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "at".toList), ("value".toList, .str "2026-09-07T13:50/2026-09-06T12:00".toList)]) = .error "badValue at" ∧
    parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "at".toList), ("value".toList, .str "9999-12-31T23:00/01:00".toList)]) = .error "badValue at" ∧
    parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "win".toList), ("value".toList, .str "25:00-13:00".toList)]) = .error "badValue win" ∧
    parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "every".toList), ("value".toList, .str "0d".toList)]) = .error "badValue every" ∧
    parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "on-event".toList), ("value".toList, .str "re ply".toList)]) = .error "badValue on-event" ∧
    parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "loc".toList), ("value".toList, .str "a b".toList)]) = .error "badValue loc" ∧
    parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "waiting".toList), ("value".toList, .str "2026-9-20".toList)]) = .error "badValue waiting" ∧
    parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "after".toList), ("value".toList, .str "^".toList)]) = .error "badValue after" :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The positive parse forms (§5.8's other direction): each bridged key's spec
value lands as `.edit` carrying that key. -/
theorem parseCmd_reads_the_bridged_keys :
    ((match parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "due".toList), ("value".toList, .str "2026-09-11".toList)]) with
      | .ok (.edit i v) => i == "t3".toList && v.key == Field.Key.due
      | _ => false) &&
     (match parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "at".toList), ("value".toList, .str "2026-09-07T12:50/13:50".toList)]) with
      | .ok (.edit i v) => i == "t3".toList && v.key == Field.Key.interval
      | _ => false) &&
     (match parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "win".toList), ("value".toList, .str "11:30-13:30".toList)]) with
      | .ok (.edit i v) => i == "t3".toList && v.key == Field.Key.window
      | _ => false) &&
     (match parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "every".toList), ("value".toList, .str "Mon,Wed,Fri".toList)]) with
      | .ok (.edit i v) => i == "t3".toList && v.key == Field.Key.every
      | _ => false) &&
     (match parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "on-event".toList), ("value".toList, .str "reply/7d".toList)]) with
      | .ok (.edit i v) => i == "t3".toList && v.key == Field.Key.onEvent
      | _ => false) &&
     (match parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "loc".toList), ("value".toList, .str "lounge".toList)]) with
      | .ok (.edit i v) => i == "t3".toList && v.key == Field.Key.loc
      | _ => false) &&
     (match parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "waiting".toList), ("value".toList, .str "2026-09-20".toList)]) with
      | .ok (.edit i v) => i == "t3".toList && v.key == Field.Key.waiting
      | _ => false) &&
     (match parseCmd (.obj [("op".toList, .str "edit".toList), ("id".toList, .str "t3".toList),
        ("key".toList, .str "after".toList), ("value".toList, .str "^m1".toList)]) with
      | .ok (.edit i v) => i == "t3".toList && v.key == Field.Key.after
      | _ => false)) = true := by decide

/-- The post-state `mapAt` re-checks is `editPost` — so when it fails `planWf`,
the name the wire carries is `editFault` read off that same plan. -/
theorem applyCmd_edit_names_the_plan_tier_fault (p : WfPlan) (i : Id) (e : Entity)
    (v : EditVal) (hget : p.val.store.get i = some e) (htab : lineHasTab e.val.line = false)
    (hbad : ∀ hs, planWf (editPost p i e v hs) = false) :
    applyCmd (.edit i v) p = .error (editFault p i v) := by
  show nameEditFault p i v (p.mapAt i (editE v)) = _
  have hm : p.mapAt i (editE v) = .error .badHorizon := by
    unfold WfPlan.mapAt
    split
    · rename_i hn; rw [hget] at hn; simp at hn
    · rename_i a hget'
      rw [hget] at hget'
      injection hget' with hget'
      subst hget'
      rw [editE_ok_of_tabless v _ htab]
      simp only
      rw [dif_neg]
      intro hc
      have := hbad (by rw [hget]; rfl)
      unfold editPost at this
      rw [hc] at this
      exact Bool.noConfusion this
  rw [hm]; rfl

theorem editFault_of_get (p : WfPlan) (i : Id) (e : Entity) (v : EditVal)
    (hget : p.val.store.get i = some e) :
    editFault p i v =
      (if !afterTotal (editPost p i e v (by rw [hget]; rfl)) then .danglingDep
       else if !afterAcyclic (editPost p i e v (by rw [hget]; rfl)) then .depCycle
       else .badHorizon) := by
  unfold editFault
  split
  · rename_i hn; rw [hget] at hn; simp at hn
  · rename_i a hget'
    rw [hget] at hget'
    injection hget' with hget'
    subst hget'
    rfl

/-- **A dangling `after:` is refused by name** (§5.8, the bite): an edit whose
post-state names an id no item carries is `danglingDep`, not `badHorizon`. -/
theorem edit_of_a_dangling_after_is_refused_by_name (p : WfPlan) (i : Id) (e : Entity)
    (ds : WfDeps) (hget : p.val.store.get i = some e) (htab : lineHasTab e.val.line = false)
    (hdang : ∀ hs, afterTotal (editPost p i e (.after ds) hs) = false) :
    applyCmd (.edit i (.after ds)) p = .error .danglingDep := by
  rw [applyCmd_edit_names_the_plan_tier_fault p i e _ hget htab (fun hs => by
    cases hw : planWf (editPost p i e (.after ds) hs) with
    | false => rfl
    | true =>
        have := (itemsWf_parts (planWf_parts hw).2.2.2.2).2.2.2.1
        rw [hdang hs] at this; exact Bool.noConfusion this)]
  rw [editFault_of_get p i e _ hget, hdang]
  rfl

/-- **A cyclic `after:` is refused by name**: a post-state whose dependencies
are all present but deadlock (§5.5) is `depCycle`. -/
theorem edit_of_a_cyclic_after_is_refused_by_name (p : WfPlan) (i : Id) (e : Entity)
    (ds : WfDeps) (hget : p.val.store.get i = some e) (htab : lineHasTab e.val.line = false)
    (htot : ∀ hs, afterTotal (editPost p i e (.after ds) hs) = true)
    (hcyc : ∀ hs, afterAcyclic (editPost p i e (.after ds) hs) = false) :
    applyCmd (.edit i (.after ds)) p = .error .depCycle := by
  rw [applyCmd_edit_names_the_plan_tier_fault p i e _ hget htab (fun hs => by
    cases hw : planWf (editPost p i e (.after ds) hs) with
    | false => rfl
    | true =>
        have := (itemsWf_parts (planWf_parts hw).2.2.2.2).2.2.2.2.1
        rw [hcyc hs] at this; exact Bool.noConfusion this)]
  rw [editFault_of_get p i e _ hget, htot, hcyc]
  rfl

/-- **…and the honest success form** (§5.8, no over-bite): with the two
dependency conjuncts holding of the post-state — the ones an `after:` edit
exists to change — and the four conjuncts an edit can break by other means
(`parentsTotal`, `parentsAcyclic`, `sectionsWf`, `shapesWf`), the edit lands,
and the stored item's `Core.after` is exactly the parsed list. -/
theorem applyCmd_after_succeeds (p : WfPlan) (i : Id) (e : Entity) (ds : WfDeps)
    (hget : p.val.store.get i = some e) (htab : lineHasTab e.val.line = false)
    (hdeps : ∀ hs, afterTotal (editPost p i e (.after ds) hs) = true ∧
      afterAcyclic (editPost p i e (.after ds) hs) = true)
    (hrest : ∀ hs, (parentsTotal (editPost p i e (.after ds) hs) &&
      parentsAcyclic (editPost p i e (.after ds) hs) &&
      sectionsWf (editPost p i e (.after ds) hs) && shapesWf (editPost p i e (.after ds) hs)) = true) :
    ∃ q : WfPlan, applyCmd (.edit i (.after ds)) p = .ok q ∧
      ∃ a : Entity, q.val.store.get i = some a ∧ a.val.after = ds.val := by
  obtain ⟨q, hq, hqi⟩ := applyCmd_edit_succeeds p i e (.after ds) hget htab (fun hs => by
    have h1 := hdeps hs
    have h2 := hrest hs
    simp only [Bool.and_eq_true] at h2
    show itemsWfButRanks (editPost p i e (.after ds) hs) = true
    simp [itemsWfButRanks, h1.1, h1.2, h2.1.1.1, h2.1.1.2, h2.1.2, h2.2])
  refine ⟨q, hq, _, hqi, ?_⟩
  exact the_edit_path_writes_what_the_field_path_reads (.after ds) e _
    (editE_ok_of_tabless _ e htab)

/-- The three `after` outcomes, decided on a loaded plan — so neither refusal
theorem's hypothesis is vacuous and the success form is reachable: a dangling
id, a two-item cycle, a self-dependency, and an `event:` dependency that
lands. -/
def depWitnessRequest : List ReqDoc :=
  [⟨"week/2026-W37.md", some ⟨week, 35⟩,
    ["# Tasks".toList, "- [ ] 3 1b Draft ^a1".toList, "- [ ] 3 1b Send after:^a1 ^b1".toList]⟩,
   ⟨"month/2026-09.md", some ⟨month, 8⟩, ["# Outcomes".toList]⟩]

def depWitnessOutcome (i : String) (k : Field.Key) (w : String) : Option (Option KErr) :=
  match loadPlan depWitnessRequest, editValOf k w.toList with
  | .ok p, some v =>
    match applyCmd (.edit i.toList v) p with
    | .ok _ => some none
    | .error e => some (some e)
  | _, _ => none

theorem the_after_refusals_are_named_on_a_loaded_plan :
    depWitnessOutcome "a1" .after "^zz" = some (some .danglingDep) ∧
    depWitnessOutcome "a1" .after "^b1" = some (some .depCycle) ∧
    depWitnessOutcome "b1" .after "^b1" = some (some .depCycle) ∧
    depWitnessOutcome "a1" .after "event:visa" = some none := by decide


/-! ## Stage 4: `close`, on plans that reach the disk (2026-09-12, stage-4 step 2)

`Close.lean` proves what a successful close does and names every refusal; this
section shows both directions fire on **loaded** plans, by decision.  Each
witness is a request `loadPlan` accepts, closed at Monday 2026-09-07 (the first
day of 2026-W37), and observed as each file's lines in rank order — the prose
and the item lines `renderDocAt` weaves, merged by rank.  (`weave` is
well-founded and does not reduce under `decide`; that the renderer writes
these lines is `the_kernel_reads_back_what_it_writes`'s business, not a close
fact.)  Every witness was probed under an 8 GB cap first (AGENTS §5.10a): the
seven together decide in about 3 s at a 1.2 GB peak. -/

/-- The free rank at the end of a file is one number, whichever module names
it: `endRank` (the close's landing) is `freshRank` (the relocating verbs'). -/
theorem foldl_max_from (xs : List Nat) : ∀ a : Nat, xs.foldl Nat.max a = Nat.max a (xs.foldl Nat.max 0) := by
  induction xs with
  | nil => intro a; simp
  | cons x t ih =>
    intro a
    simp only [List.foldl_cons]
    rw [ih (Nat.max a x), ih (Nat.max 0 x)]
    show max (max a x) _ = max a (max (max 0 x) _)
    rw [Nat.zero_max, Nat.max_assoc]

theorem endRank_is_freshRank (p : PlanCore) (k : DocIx) : endRank p k = freshRank p k := by
  unfold endRank freshRank docRanks docProseMax docLineMax
  rw [List.foldl_append, foldl_max_from]
  congr 1
  congr 1
  · cases p.docs[k]? with
    | none => rfl
    | some d => simp [List.foldl_map]
  · simp [List.foldl_map]

def closeNow : Day := Cal.toDay ⟨2026, 9, 7⟩
def closeW36 : Region := ⟨week, Cal.weekOrdinal (Cal.toDay ⟨2026, 8, 31⟩)⟩
def closeW37 : Region := ⟨week, Cal.weekOrdinal closeNow⟩
def closeM08 : Region := ⟨month, Cal.monthOrdinal (Cal.toDay ⟨2026, 8, 1⟩)⟩
def closeM09 : Region := ⟨month, Cal.monthOrdinal closeNow⟩

/-- The loaded plan of a request, if it loads. -/
def loadedPlan? (docs : List ReqDoc) : Option WfPlan :=
  match loadPlan docs with
  | .ok p    => some p
  | .error _ => none

/-- Each file's lines in rank order: the prose and the item lines `renderDocAt`
weaves, merged by rank.  The one observation every close witness reads. -/
def fileLinesOf (q : WfPlan) : List (List (List Char)) :=
  q.val.docs.zipIdx.map (fun dk =>
    (sortByRank (dk.1.prose ++ (q.val.lines.filter (fun l => l.site.doc == dk.2)).map
      (fun l => (l.site.rank, l.text)))).map Prod.snd)

/-- A close's result, observed: each file's lines if it succeeded. -/
def closeResultLines : Except KErr WfPlan → Option (List (List (List Char)))
  | .ok q    => some (fileLinesOf q)
  | .error _ => none

/-- Each file's lines in rank order after `close g closeNow`, if the request
loads and the close succeeds. -/
def closedFileLines (g : Grain) (docs : List ReqDoc) : Option (List (List (List Char))) :=
  (loadedPlan? docs).bind (fun p => closeResultLines (close g closeNow 50 p))

/-- The close's refusal, if the request loads and the close refuses. -/
def closeRefusal (g : Grain) (docs : List ReqDoc) : Option KErr :=
  (loadedPlan? docs).bind (fun p =>
    match close g closeNow 50 p with
    | .ok _    => none
    | .error k => some k)

/-- 2026-W36 with an open item, a done item, a wall still ahead and a recurring
line; the live week; and a month file whose `# Demoted` is followed by another
section, so the landing has to shift to make room. -/
def closeWeekWitness : List ReqDoc :=
  [⟨"week/2026-W36.md", some closeW36,
     ["# Tasks".toList,
      "- [ ] 4 6b Rollback path passes tests ^m2".toList,
      "- [x] 2 1b Send the draft ^t1".toList,
      "- [ ] 5 2h Midterm at:2026-10-20T10:00/12:00 ^x1".toList,
      "- [ ] 1 15m Standup every:day ^r1".toList]⟩,
   ⟨"week/2026-W37.md", some closeW37, ["# Tasks".toList]⟩,
   ⟨"month/2026-09.md", some closeM09,
     ["# Outcomes".toList, "- [ ] 5 !1 Lean through ch.8 ^O1".toList, "# Demoted".toList,
      "# Notes".toList]⟩]

set_option maxRecDepth 40000 in
/-- **§6.3's week row, on a loaded plan.**  The open line stays behind as a `[-]`
tombstone **in its own bytes** and its stamped record lands at the end of the
month's `# Demoted`, ahead of `# Notes` — the legitimately-differing pair gap 31
was about, written by the kernel.  The done line stays; the recurring line
stays; the wall still ahead is carried, undemoted, into the live week (F4). -/
theorem the_week_close_copies_carries_and_leaves_the_rest :
    closedFileLines week closeWeekWitness = some
      [["# Tasks".toList, "- [-] 4 6b Rollback path passes tests ^m2".toList,
        "- [x] 2 1b Send the draft ^t1".toList, "- [ ] 1 15m Standup every:day ^r1".toList],
       ["# Tasks".toList, "- [ ] 5 2h Midterm at:2026-10-20T10:00/12:00 ^x1".toList],
       ["# Outcomes".toList, "- [ ] 5 !1 Lean through ch.8 ^O1".toList, "# Demoted".toList,
        "- [-] 4 6b Rollback path passes tests demoted:W36 ^m2".toList, "# Notes".toList]] := by
  decide

/-- A day file of Friday 2026-09-04 — in 2026-W36 — closed on Monday: both
weeks' files are handed over. -/
def closeDayWitness : List ReqDoc :=
  [⟨"day/2026-09-04.md", some ⟨day, Cal.toDay ⟨2026, 9, 4⟩⟩,
     ["# Pinned".toList, "- [>] 2 20m Call the bank ^p1".toList,
      "- [x] 1 10m Water the plants ^p2".toList]⟩,
   ⟨"week/2026-W36.md", some closeW36, ["# Tasks".toList]⟩,
   ⟨"week/2026-W37.md", some closeW37,
     ["# Tasks".toList, "- [ ] 3 1b Review the drafts ^t5".toList]⟩]

set_option maxRecDepth 40000 in
/-- **§6.3's day row, and D1, on a loaded plan.**  The pinned `[>]` reopens to
`[ ]`, gains `demoted:D04`, and moves to the week containing *now* — 2026-W37 —
and not to 2026-W36, the week the closed day belonged to, whose file is right
there.  The done line stays. -/
theorem the_day_close_files_into_the_week_of_now :
    closedFileLines day closeDayWitness = some
      [["# Pinned".toList, "- [x] 1 10m Water the plants ^p2".toList],
       ["# Tasks".toList],
       ["# Tasks".toList, "- [ ] 3 1b Review the drafts ^t5".toList,
        "- [ ] 2 20m Call the bank demoted:D04 ^p1".toList]] := by
  decide

def closeMonthWitness : List ReqDoc :=
  [⟨"month/2026-08.md", some closeM08,
     ["# Outcomes".toList, "- [ ] 5 !1 Old outcome ^O7".toList,
      "- [x] 3 !2 Done outcome ^O8".toList,
      "# Demoted".toList, "- [-] 4 3b Carried record est:3b demoted:W33 ^m9".toList]⟩,
   ⟨"month/2026-09.md", some closeM09,
     ["# Outcomes".toList, "- [ ] 5 !1 Lean through ch.8 ^O1".toList, "# Demoted".toList]⟩]

set_option maxRecDepth 40000 in
/-- **§6.3's month row, on a loaded plan.**  The open outcome moves into the next
month's `# Outcomes` (a shift makes room ahead of `# Demoted`), keeping `!1`;
the `[-]` record moves into its `# Demoted`, keeping its stamp and its `est:`;
the done outcome stays. -/
theorem the_month_close_moves_each_line_into_its_section :
    closedFileLines month closeMonthWitness = some
      [["# Outcomes".toList, "- [x] 3 !2 Done outcome ^O8".toList, "# Demoted".toList],
       ["# Outcomes".toList, "- [ ] 5 !1 Lean through ch.8 ^O1".toList,
        "- [ ] 5 !1 Old outcome ^O7".toList,
        "# Demoted".toList, "- [-] 4 3b Carried record est:3b demoted:W33 ^m9".toList]] := by
  decide

def closeDatedWitness : List ReqDoc :=
  [⟨"week/2026-W36.md", some closeW36,
     ["# Tasks".toList, "- [ ] 4 2b Pset due:2026-09-04 ^d1".toList]⟩,
   ⟨"month/2026-09.md", some closeM09, ["# Outcomes".toList, "# Demoted".toList]⟩]

def closeNoMonthWitness : List ReqDoc :=
  [⟨"week/2026-W36.md", some closeW36, ["# Tasks".toList, "- [ ] 4 2b Pset ^d1".toList]⟩]

def closeNoDemotedWitness : List ReqDoc :=
  [⟨"week/2026-W36.md", some closeW36, ["# Tasks".toList, "- [ ] 4 2b Pset ^d1".toList]⟩,
   ⟨"month/2026-09.md", some closeM09, ["# Outcomes".toList]⟩]

/-- The week witness without the live week's file: its wall has nowhere to be
carried. -/
def closeNoLiveWeekWitness : List ReqDoc :=
  closeWeekWitness.filter (fun d => d.path != "week/2026-W37.md")

/-- §4.3's own pair — the `[ ]` record in a week, its `[-]` copy under the month's
`# Demoted` — with the week moved to 2026-W36 so that Monday closes it, and the
outcome `^O2` both lines name above the month's `# Demoted` (D6: without it the
request does not load, `danglingParent`). -/
def closePreClosePairWitness : List ReqDoc :=
  [⟨"week/2026-W36.md", some closeW36,
     ["# Milestones".toList, "- [ ] 4 6b Rollback path passes tests   @O2 ^m2".toList]⟩,
   ⟨"month/2026-09.md", some closeM09,
     ["# Outcomes".toList, "- [ ] 4 !1 Soundcode: end-to-end demo runs             ^O2".toList, "# Demoted".toList,
      "- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2".toList]⟩]

def closeW35 : Region := ⟨week, Cal.weekOrdinal (Cal.toDay ⟨2026, 8, 24⟩)⟩

/-- 2026-W35, closed, holding `^m4`'s `[-]` line — not a `# Demoted` record —
beside the open `^m4` line of 2026-W36 (a hand edit: `readopt` removes both lines),
and a September with an empty `# Demoted` under the outcome `^O3` both lines name
(D6). -/
def closeStrayTombWitness : List ReqDoc :=
  [⟨"week/2026-W35.md", some closeW35,
     ["# Milestones".toList, "- [-] 2 Pick winter courses @O3 demoted:W34 ^m4".toList]⟩,
   ⟨"week/2026-W36.md", some closeW36,
     ["# Milestones".toList, "- [ ] 2 Pick winter courses @O3 ^m4".toList]⟩,
   ⟨"month/2026-09.md", some closeM09, ["# Outcomes".toList, "- [ ] 2 !3 Winter course selection + admin done        ^O3".toList, "# Demoted".toList]⟩]

/-- `closeDatedWitness` with a backlog that has no `# Overdue` section. -/
def closeOverdueNoSectionWitness : List ReqDoc :=
  closeDatedWitness ++
    [⟨"backlog.md", none, ["# Untied".toList, "- [ ] 2 30m Insurance claim ^a1".toList]⟩]

set_option maxRecDepth 40000 in
/-- **The check bites, by name, on loaded plans** — the refusals a week close has
left since the owner's D7 and D8.  A past-due dated line with no backlog in the
request is `noTarget`, and one whose backlog has no `# Overdue` is `noSection`
(the kernel does not create a section; the host hands it over, README gap 56); a
week close with no month file is `noTarget`, and so is one with a wall to carry
and no live week; a month file with no `# Demoted` is `noSection`; an open line
whose item's tombstone is a `[-]` line in an earlier week rather than a `# Demoted`
record is `alreadyDemoted` (`closeOne_never_merges_into_a_stray_tomb`).  None of
them is a close that silently skipped a line.  (Restates
`each_close_refusal_is_named_on_a_loaded_plan`, whose first conjunct — the dated
line ↦ `badHorizon`, README gap 55 — is false since D7:
`a_dated_line_no_longer_refuses_the_week_close_as_badHorizon`.) -/
theorem the_close_refusals_left_after_d7_are_named_on_loaded_plans :
    closeRefusal week closeDatedWitness = some .noTarget ∧
      closeRefusal week closeOverdueNoSectionWitness = some .noSection ∧
      closeRefusal week closeNoMonthWitness = some .noTarget ∧
      closeRefusal week closeNoLiveWeekWitness = some .noTarget ∧
      closeRefusal week closeNoDemotedWitness = some .noSection ∧
      closeRefusal week closeStrayTombWitness = some .alreadyDemoted := by
  decide

/-- **`each_close_refusal_is_named_on_a_loaded_plan`, refuted since D7** (README gap
55, closed).  Its first conjunct said an open dated line in an ended week refuses
the week close `badHorizon`, because its record broke the month rule; the line is
now routed — past due to the backlog (D7), not yet due into `# Demoted` with its
date (D8) — and the one refusal left for it is a missing destination. -/
theorem a_dated_line_no_longer_refuses_the_week_close_as_badHorizon :
    ¬ (closeRefusal week closeDatedWitness = some .badHorizon ∧
      closeRefusal week closeNoMonthWitness = some .noTarget ∧
      closeRefusal week closeNoLiveWeekWitness = some .noTarget ∧
      closeRefusal week closeNoDemotedWitness = some .noSection ∧
      closeRefusal week closeStrayTombWitness = some .alreadyDemoted) := by
  intro h
  have h1 := h.1
  rw [the_close_refusals_left_after_d7_are_named_on_loaded_plans.1] at h1
  cases h1

set_option maxRecDepth 40000 in
/-- §4.3's pre-close pair loads and closes: no refusal.  The first conjunct is new
at D6: `closeRefusal` is `none` for a request that does not load too, and with
`@O2` dangling this statement held for that reason alone. -/
theorem the_pre_close_pair_closes_on_a_loaded_plan :
    loadsOk closePreClosePairWitness = true ∧
      closeRefusal week closePreClosePairWitness = none := by decide

/-- **`the_close_refusals_are_named_on_loaded_plans`, as it stood before gap 53,
refuted.** -/
theorem the_pre_close_pair_is_not_a_named_refusal :
    ¬ (closeRefusal week closeDatedWitness = some .badHorizon ∧
      closeRefusal week closeNoMonthWitness = some .noTarget ∧
      closeRefusal week closeNoLiveWeekWitness = some .noTarget ∧
      closeRefusal week closeNoDemotedWitness = some .noSection ∧
      closeRefusal week closePreClosePairWitness = some .alreadyDemoted) := by
  intro h
  have h5 := h.2.2.2.2
  rw [the_pre_close_pair_closes_on_a_loaded_plan.2] at h5
  cases h5

/-! ## L17, refuted: `close week` and `close month` do not commute (stage-4 step 3)

**Why they differ, in one sentence:** both closes file into the one open month
containing *now* and each lands its line at the end of that month's `# Demoted`,
so whichever close runs second lands its line below the other's.

The goal expected a different reason — that the week close's output becomes the
month close's input in one order and not the other — and that reason is gone
with D1: at one instant no close's output is in a closed region
(`stepSkel_lands_outside_every_closed_region`), so the two orders agree on every
line's file, box, bytes and tombstone (`two_closes_at_one_instant_commute_on_skeletons`,
Close.lean) and differ **only in rank**.  For `autoClose` this means the order of
the grains decides the order of lines inside a shared destination section, and
nothing else.

The witness: 2026-W36 with one open line, 2026-08 with one `[-]` record under
`# Demoted`, and 2026-09 with an empty `# Demoted`, closed at Monday 2026-09-07
(W36 and August both closed).  Probed under an 8 GB cap first: both orders and
the L27 pair below decide together in under 3 s at a 1.1 GB peak. -/

def closeCommuteWitness : List ReqDoc :=
  [⟨"week/2026-W36.md", some closeW36,
     ["# Tasks".toList, "- [ ] 4 6b Rollback path passes tests ^m2".toList]⟩,
   ⟨"month/2026-08.md", some closeM08,
     ["# Outcomes".toList,
      "# Demoted".toList, "- [-] 4 3b Carried record est:3b demoted:W33 ^m9".toList]⟩,
   ⟨"month/2026-09.md", some closeM09, ["# Outcomes".toList, "# Demoted".toList]⟩]

theorem the_close_commute_witness_loads : loadsOk closeCommuteWitness = true := by decide

/-- The loaded witness plan.  Total by `the_close_commute_witness_loads`: the
error branch is refuted, not defaulted. -/
def closeCommutePlan : WfPlan :=
  match h : loadPlan closeCommuteWitness with
  | .ok p => p
  | .error _ => absurd the_close_commute_witness_loads (by simp [loadsOk, h])

set_option maxRecDepth 40000 in
/-- **Week, then month.**  `^m2`'s stamped record lands at the end of 2026-09's
`# Demoted`; then the month close moves `^m9` there, below it. -/
theorem the_week_then_month_close_lands_the_week_record_first :
    closeResultLines ((close week closeNow 50 closeCommutePlan).bind (close month closeNow 50)) = some
      [["# Tasks".toList, "- [-] 4 6b Rollback path passes tests ^m2".toList],
       ["# Outcomes".toList, "# Demoted".toList],
       ["# Outcomes".toList, "# Demoted".toList,
        "- [-] 4 6b Rollback path passes tests demoted:W36 ^m2".toList,
        "- [-] 4 3b Carried record est:3b demoted:W33 ^m9".toList]] := by
  decide

set_option maxRecDepth 40000 in
/-- **Month, then week.**  The same lines in the same files, and `^m9` above
`^m2`. -/
theorem the_month_then_week_close_lands_the_month_record_first :
    closeResultLines ((close month closeNow 50 closeCommutePlan).bind (close week closeNow 50)) = some
      [["# Tasks".toList, "- [-] 4 6b Rollback path passes tests ^m2".toList],
       ["# Outcomes".toList, "# Demoted".toList],
       ["# Outcomes".toList, "# Demoted".toList,
        "- [-] 4 3b Carried record est:3b demoted:W33 ^m9".toList,
        "- [-] 4 6b Rollback path passes tests demoted:W36 ^m2".toList]] := by
  decide

/-- Both orders succeed on one loaded plan at one instant, and their plans
differ.  This is also the witness that the hypotheses of
`two_closes_at_one_instant_commute_on_skeletons` are satisfiable at week and
month. -/
theorem close_week_month_orders_both_succeed_and_differ :
    ∃ (now : Day) (bm : Nat) (p q r : WfPlan),
      (close week now bm p).bind (close month now bm) = .ok q ∧
        (close month now bm p).bind (close week now bm) = .ok r ∧ q ≠ r := by
  have hwm := the_week_then_month_close_lands_the_week_record_first
  have hmw := the_month_then_week_close_lands_the_month_record_first
  cases h1 : (close week closeNow 50 closeCommutePlan).bind (close month closeNow 50) with
  | error x => rw [h1] at hwm; simp [closeResultLines] at hwm
  | ok q =>
    cases h2 : (close month closeNow 50 closeCommutePlan).bind (close week closeNow 50) with
    | error x => rw [h2] at hmw; simp [closeResultLines] at hmw
    | ok r =>
      refine ⟨closeNow, 50, closeCommutePlan, q, r, h1, h2, fun hqr => ?_⟩
      rw [h1, hqr] at hwm
      rw [h2, hwm] at hmw
      exact absurd hmw (by decide)

/-- **L17 (R\*), refuted — discharged from `Goals.lean` by refute-and-rename.**
The negation of `close_week_and_close_month_commute`, quantifier for quantifier:
it is not the case that for every instant and every plan the two orders give the
same result.  Why, and what does commute: this section's header. -/
theorem close_week_and_close_month_do_not_commute :
    ¬ ∀ (now : Day) (bm : Nat) (p : WfPlan),
      (close week now bm p).bind (close month now bm) = (close month now bm p).bind (close week now bm) := by
  intro hall
  obtain ⟨now, bm, p, q, r, h1, h2, hqr⟩ := close_week_month_orders_both_succeed_and_differ
  rw [hall now bm p, h2] at h1
  injection h1 with h
  exact hqr h.symm

/-! ## L27, refuted: lifecycle commands do not commute (stage-4 step 3)

**Why, in one sentence:** `readopt` reopens only a demoted record
(`readopt_of_a_live_record_is_refused`) and `demote` is what makes one, so the
order of a demote/readopt pair at one id is observable as success against a
named refusal.

This refutes the law as written and answers nothing else.  Whether lifecycle
pairs that **both succeed** ought to commute — `inventory`'s R7, `demote ^m1 ;
move ^m1 week` against its reverse — is a product question, AGENTS §10.5 q7,
the owner's, assigned to stage 6; a refutation by precondition does not bear on
it.  The witness is `undoWitnessPlan` (L22's), unchanged. -/

/-- A request's refusal, if `applyAll` refuses it. -/
def cmdsRefusal (cs : List ReqCmd) (p : WfPlan) : Option KErr :=
  match applyAll cs p with
  | .ok _    => none
  | .error k => some k

/-- Demote `^m1` into the month, then readopt it into the week: both succeed.
The reverse: `readopt` answers `notDemoted` and the demote never runs. -/
theorem demote_then_readopt_succeeds_and_the_reverse_is_refused :
    cmdsRefusal [.demote "m1".toList 1 (.week 37), .readopt "m1".toList 0] undoWitnessPlan = none ∧
      cmdsRefusal [.readopt "m1".toList 0, .demote "m1".toList 1 (.week 37)] undoWitnessPlan =
        some .notDemoted := by
  decide

/-- **L27 (R\*), refuted — discharged from `Goals.lean` by refute-and-rename.**
The negation of `lifecycle_commands_commute`, quantifier for quantifier. -/
theorem lifecycle_commands_do_not_commute :
    ¬ ∀ (c d : ReqCmd) (p : WfPlan), applyAll [c, d] p = applyAll [d, c] p := by
  intro hall
  obtain ⟨h1, h2⟩ := demote_then_readopt_succeeds_and_the_reverse_is_refused
  have heq : cmdsRefusal [.demote "m1".toList 1 (.week 37), .readopt "m1".toList 0] undoWitnessPlan
      = cmdsRefusal [.readopt "m1".toList 0, .demote "m1".toList 1 (.week 37)] undoWitnessPlan := by
    unfold cmdsRefusal
    rw [hall]
  rw [heq, h2] at h1
  exact absurd h1 (by simp)

/-! ## `autoClose` on a tree three months stale (stage-4 step 4)

The owner drove the shipped Rust over stale trees (2026-09-12).  Three months
stale, fork-point `auto_close` caught up the week and month grains but ran
**zero** day closes — `catch_up` looked at the sixteen most recent days, none of
which had a file — so every pinned item older than sixteen days stayed in its
sealed day file while `tm check` reported no problems.  Fourteen days stale, the
opposite: a day's leftovers were filed into a week the next iteration closed,
and each gained two stamps.

The witness below has both shapes in one tree, closed at Saturday 2026-09-12:
a pinned `[>]` of 2026-06-12 (three months) and one of 2026-08-29 (fourteen
days, in 2026-W35), open week lines in 2026-W24 and 2026-W35, a wall still ahead
in 2026-W35, a June month file with an open outcome and a `[-]` record, and the
live week and month.  One `autoClose` call files every unfinished line into a
region containing *now*, each with **at most one** new stamp, keeps every id and
the summed estimate, and leaves behind in closed files exactly the lines §6.3
leaves: a done day item, a done week item, a recurring line and a done outcome.
Probed under an 8 GB cap first (AGENTS §5.10a): the three observations decide in
about 8 s at a 1.7 GB peak, imports included. -/

def staleNow : Day := Cal.toDay ⟨2026, 9, 12⟩
def staleW24 : Region := ⟨week, Cal.weekOrdinal (Cal.toDay ⟨2026, 6, 8⟩)⟩
def staleW35 : Region := ⟨week, Cal.weekOrdinal (Cal.toDay ⟨2026, 8, 24⟩)⟩
def staleW37 : Region := ⟨week, Cal.weekOrdinal staleNow⟩
def staleM06 : Region := ⟨month, Cal.monthOrdinal (Cal.toDay ⟨2026, 6, 1⟩)⟩
def staleM09 : Region := ⟨month, Cal.monthOrdinal staleNow⟩

/-- A tree last closed in June, with the two stale shapes the owner measured. -/
def staleWitness : List ReqDoc :=
  [⟨"day/2026-06-12.md", some ⟨day, Cal.toDay ⟨2026, 6, 12⟩⟩,
     ["# Pinned".toList, "- [>] 2 20m Call the bank ^p1".toList,
      "- [x] 1 10m Water the plants ^p2".toList]⟩,
   ⟨"day/2026-08-29.md", some ⟨day, Cal.toDay ⟨2026, 8, 29⟩⟩,
     ["# Pinned".toList, "- [>] 3 1h Draft the letter ^p3".toList]⟩,
   ⟨"week/2026-W24.md", some staleW24,
     ["# Tasks".toList,
      "- [ ] 4 6b Rollback path passes tests ^m2".toList,
      "- [x] 2 1b Send the draft ^t1".toList,
      "- [ ] 1 15m Standup every:day ^r1".toList]⟩,
   ⟨"week/2026-W35.md", some staleW35,
     ["# Tasks".toList,
      "- [ ] 3 2b Read chapter four ^m3".toList,
      "- [ ] 5 2h Midterm at:2026-10-20T10:00/12:00 ^x1".toList]⟩,
   ⟨"week/2026-W37.md", some staleW37,
     ["# Tasks".toList, "- [ ] 3 1b Review the drafts ^t5".toList]⟩,
   ⟨"month/2026-06.md", some staleM06,
     ["# Outcomes".toList, "- [ ] 5 !1 Old outcome ^O7".toList,
      "- [x] 3 !2 Done outcome ^O8".toList,
      "# Demoted".toList, "- [-] 4 3b Carried record est:3b demoted:W22 ^m9".toList]⟩,
   ⟨"month/2026-09.md", some staleM09,
     ["# Outcomes".toList, "- [ ] 5 !1 Lean through ch.8 ^O1".toList, "# Demoted".toList]⟩]

theorem the_stale_witness_loads : loadsOk staleWitness = true := by decide

/-- The loaded stale plan.  Total by `the_stale_witness_loads`: the error branch
is refuted, not defaulted. -/
def stalePlan : WfPlan :=
  match h : loadPlan staleWitness with
  | .ok p => p
  | .error _ => absurd the_stale_witness_loads (by simp [loadsOk, h])

/-- One row per item, in store order: its id, the path of the file its record is
in, how many stamps it carries, and its estimate in minutes at a 50-minute block
(0 when it has none). -/
def itemLedger (q : WfPlan) : List (Id × List Char × Nat × Nat) :=
  q.val.store.dom.filterMap (fun i => (q.val.store.get i).map (fun e =>
    (i, ((q.val.docs[e.val.live.doc]?).map Doc.path).getD [], e.val.stamps.length,
     (e.val.est.map (Field.Dur.minutes 50)).getD 0)))

/-- The summed estimate of a ledger, in minutes. -/
def ledgerMinutes (l : List (Id × List Char × Nat × Nat)) : Nat := (l.map (fun r => r.2.2.2)).sum

/-- The ids whose record sits in a file whose region is closed at `now`. -/
def closedLiveIds (now : Day) (q : WfPlan) : List Id :=
  q.val.store.dom.filter (fun i =>
    match q.val.store.get i with
    | none   => false
    | some e =>
      match docRegion q.val e.val.live.doc with
      | none   => false
      | some r => decide (Closed r now))

theorem mem_closedLiveIds {now : Day} {q : WfPlan} {i : Id} (h : i ∈ closedLiveIds now q) :
    ∃ e r, q.val.store.get i = some e ∧ docRegion q.val e.val.live.doc = some r ∧ Closed r now := by
  unfold closedLiveIds at h
  have hf := (List.mem_filter.1 h).2
  revert hf
  cases hg : q.val.store.get i with
  | none => simp
  | some e =>
    cases hr : docRegion q.val e.val.live.doc with
    | none => simp [hr]
    | some r =>
      simp only [hr, decide_eq_true_eq]
      exact fun hc => ⟨e, r, rfl, hr, hc⟩

/-- The stale plan after one `autoClose`, observed three ways. -/
def staleCaughtUp {α : Type} (obs : WfPlan → α) : Option α :=
  match autoClose staleNow 50 stalePlan with
  | .ok q    => some (obs q)
  | .error _ => none

/-- The three observations of a caught-up plan, as one value, so that the stale
plan is closed once per decision rather than once per observation. -/
structure CatchUpView where
  lines    : List (List (List Char))
  ledger   : List (Id × List Char × Nat × Nat)
  stranded : List Id
deriving DecidableEq

def catchUpView (now : Day) (q : WfPlan) : CatchUpView :=
  ⟨fileLinesOf q, itemLedger q, closedLiveIds now q⟩

set_option maxRecDepth 40000 in
/-- The stale plan after one `autoClose`: each file's lines, the item ledger, and
the ids left in closed files — decided together; the three theorems below read
their halves off it.  Since gap 59's fix the lines one close lands in one file
arrive in source order — documents in request order, then rank: `^p1` (the June
day) ahead of `^p3` (the August day) in 2026-W37, and `^m2` (2026-W24) ahead of
`^m3` (2026-W35) in the month's `# Demoted`; before it both pairs were
reversed. -/
theorem the_stale_catch_up_observed :
    staleCaughtUp (catchUpView staleNow) = some
      ⟨[["# Pinned".toList, "- [x] 1 10m Water the plants ^p2".toList],
       ["# Pinned".toList],
       ["# Tasks".toList, "- [-] 4 6b Rollback path passes tests ^m2".toList,
        "- [x] 2 1b Send the draft ^t1".toList, "- [ ] 1 15m Standup every:day ^r1".toList],
       ["# Tasks".toList, "- [-] 3 2b Read chapter four ^m3".toList],
       ["# Tasks".toList, "- [ ] 3 1b Review the drafts ^t5".toList,
        "- [ ] 2 20m Call the bank demoted:D12 ^p1".toList,
        "- [ ] 3 1h Draft the letter demoted:D29 ^p3".toList,
        "- [ ] 5 2h Midterm at:2026-10-20T10:00/12:00 ^x1".toList],
       ["# Outcomes".toList, "- [x] 3 !2 Done outcome ^O8".toList, "# Demoted".toList],
       ["# Outcomes".toList, "- [ ] 5 !1 Lean through ch.8 ^O1".toList,
        "- [ ] 5 !1 Old outcome ^O7".toList, "# Demoted".toList,
        "- [-] 4 6b Rollback path passes tests demoted:W24 ^m2".toList,
        "- [-] 3 2b Read chapter four demoted:W35 ^m3".toList,
        "- [-] 4 3b Carried record est:3b demoted:W22 ^m9".toList]],
       [("O1".toList, "month/2026-09.md".toList, 0, 0),
       ("m9".toList, "month/2026-09.md".toList, 1, 150),
       ("O8".toList, "month/2026-06.md".toList, 0, 0),
       ("O7".toList, "month/2026-09.md".toList, 0, 0),
       ("t5".toList, "week/2026-W37.md".toList, 0, 50),
       ("x1".toList, "week/2026-W37.md".toList, 0, 120),
       ("m3".toList, "month/2026-09.md".toList, 1, 100),
       ("r1".toList, "week/2026-W24.md".toList, 0, 15),
       ("t1".toList, "week/2026-W24.md".toList, 0, 50),
       ("m2".toList, "month/2026-09.md".toList, 1, 300),
       ("p3".toList, "week/2026-W37.md".toList, 1, 60),
       ("p2".toList, "day/2026-06-12.md".toList, 0, 10),
       ("p1".toList, "week/2026-W37.md".toList, 1, 20)],
       ["O8".toList, "r1".toList, "t1".toList, "p2".toList]⟩ := by
  decide

/-- Reading one field of the decided view. -/
theorem staleCaughtUp_map {α : Type} (obs : CatchUpView → α) :
    staleCaughtUp (fun q => obs (catchUpView staleNow q)) =
      (staleCaughtUp (catchUpView staleNow)).map obs := by
  unfold staleCaughtUp
  cases autoClose staleNow 50 stalePlan <;> rfl

/-- **A three-month-stale tree catches up in one call** (AGENTS §8.2's
acceptance, the library half).  Both pinned items — the three-month one and the
fourteen-day one — reopen and land in **2026-W37**, the week containing *now*,
with one day stamp each (`D12`, `D29`); both open week lines leave `[-]`
tombstones and land in 2026-09's `# Demoted` with one week stamp each (`W24`,
`W35`); the wall still ahead is carried into 2026-W37 unstamped; June's open
outcome and its `[-]` record move into 2026-09's sections unchanged.  What stays
in a closed file is done, recurring, or a tombstone. -/
theorem the_stale_tree_catches_up_in_one_call :
    staleCaughtUp fileLinesOf = some
      [["# Pinned".toList, "- [x] 1 10m Water the plants ^p2".toList],
       ["# Pinned".toList],
       ["# Tasks".toList, "- [-] 4 6b Rollback path passes tests ^m2".toList,
        "- [x] 2 1b Send the draft ^t1".toList, "- [ ] 1 15m Standup every:day ^r1".toList],
       ["# Tasks".toList, "- [-] 3 2b Read chapter four ^m3".toList],
       ["# Tasks".toList, "- [ ] 3 1b Review the drafts ^t5".toList,
        "- [ ] 2 20m Call the bank demoted:D12 ^p1".toList,
        "- [ ] 3 1h Draft the letter demoted:D29 ^p3".toList,
        "- [ ] 5 2h Midterm at:2026-10-20T10:00/12:00 ^x1".toList],
       ["# Outcomes".toList, "- [x] 3 !2 Done outcome ^O8".toList, "# Demoted".toList],
       ["# Outcomes".toList, "- [ ] 5 !1 Lean through ch.8 ^O1".toList,
        "- [ ] 5 !1 Old outcome ^O7".toList, "# Demoted".toList,
        "- [-] 4 6b Rollback path passes tests demoted:W24 ^m2".toList,
        "- [-] 3 2b Read chapter four demoted:W35 ^m3".toList,
        "- [-] 4 3b Carried record est:3b demoted:W22 ^m9".toList]] :=
  (staleCaughtUp_map CatchUpView.lines).trans (by rw [the_stale_catch_up_observed]; rfl)

set_option maxRecDepth 40000 in
/-- The stale plan's items before the call: thirteen ids, 875 minutes. -/
theorem the_stale_ledger_before_catch_up :
    itemLedger stalePlan =
      [("O1".toList, "month/2026-09.md".toList, 0, 0),
       ("m9".toList, "month/2026-06.md".toList, 1, 150),
       ("O8".toList, "month/2026-06.md".toList, 0, 0),
       ("O7".toList, "month/2026-06.md".toList, 0, 0),
       ("t5".toList, "week/2026-W37.md".toList, 0, 50),
       ("x1".toList, "week/2026-W35.md".toList, 0, 120),
       ("m3".toList, "week/2026-W35.md".toList, 0, 100),
       ("r1".toList, "week/2026-W24.md".toList, 0, 15),
       ("t1".toList, "week/2026-W24.md".toList, 0, 50),
       ("m2".toList, "week/2026-W24.md".toList, 0, 300),
       ("p3".toList, "day/2026-08-29.md".toList, 0, 60),
       ("p2".toList, "day/2026-06-12.md".toList, 0, 10),
       ("p1".toList, "day/2026-06-12.md".toList, 0, 20)] := by
  decide

/-- The same items after one `autoClose`: every id still there, every estimate
the same, four lines with exactly one new stamp and none with two. -/
theorem the_stale_ledger_after_catch_up :
    staleCaughtUp itemLedger = some
      [("O1".toList, "month/2026-09.md".toList, 0, 0),
       ("m9".toList, "month/2026-09.md".toList, 1, 150),
       ("O8".toList, "month/2026-06.md".toList, 0, 0),
       ("O7".toList, "month/2026-09.md".toList, 0, 0),
       ("t5".toList, "week/2026-W37.md".toList, 0, 50),
       ("x1".toList, "week/2026-W37.md".toList, 0, 120),
       ("m3".toList, "month/2026-09.md".toList, 1, 100),
       ("r1".toList, "week/2026-W24.md".toList, 0, 15),
       ("t1".toList, "week/2026-W24.md".toList, 0, 50),
       ("m2".toList, "month/2026-09.md".toList, 1, 300),
       ("p3".toList, "week/2026-W37.md".toList, 1, 60),
       ("p2".toList, "day/2026-06-12.md".toList, 0, 10),
       ("p1".toList, "week/2026-W37.md".toList, 1, 20)] :=
  (staleCaughtUp_map CatchUpView.ledger).trans (by rw [the_stale_catch_up_observed]; rfl)

/-- **"A 3-month-stale tree catches up losing nothing"**, at library level: the
same ids in the same order, the summed estimate unchanged at 875 minutes, and no
item's stamp count up by more than one. -/
theorem the_stale_tree_catches_up_losing_nothing :
    staleCaughtUp (fun q => (itemLedger q).map (fun r => r.1)) =
        some ((itemLedger stalePlan).map (fun r => r.1)) ∧
      staleCaughtUp (fun q => ledgerMinutes (itemLedger q)) =
        some (ledgerMinutes (itemLedger stalePlan)) ∧
      ledgerMinutes (itemLedger stalePlan) = 875 ∧
      staleCaughtUp (fun q => ((itemLedger q).zip (itemLedger stalePlan)).all
        (fun ab => ab.1.2.2.1 ≤ ab.2.2.2.1 + 1)) = some true := by
  have hb := the_stale_ledger_before_catch_up
  have ha := the_stale_ledger_after_catch_up
  unfold staleCaughtUp at ha ⊢
  cases h : autoClose staleNow 50 stalePlan with
  | error x => rw [h] at ha; simp at ha
  | ok q =>
    rw [h] at ha
    simp only [Option.some.injEq] at ha ⊢
    rw [ha, hb]
    decide

/-- What one `autoClose` leaves in closed files: the done day item, the done
and recurring week items, and the done outcome — the lines §6.3 leaves. -/
theorem the_stale_catch_up_leaves_only_settled_and_recurring_lines :
    staleCaughtUp (closedLiveIds staleNow) =
      some ["O8".toList, "r1".toList, "t1".toList, "p2".toList] :=
  (staleCaughtUp_map CatchUpView.stranded).trans (by rw [the_stale_catch_up_observed]; rfl)

/-- **L19c (P\*), refuted — discharged from `Goals.lean` by refute-and-rename.**
The negation of `autoClose_runs_every_period_it_passes`, quantifier for
quantifier: it is not the case that after every successful `autoClose` no live
line sits in a closed region.  `^t1`, a `[x]` line of the closed 2026-W24, is
where §6.3 leaves it.  What does hold is `autoClose_strands_no_unfinished_line`
(Close.lean): nothing a close takes is left behind, at any grain. -/
theorem autoClose_leaves_lines_in_periods_it_passes :
    ¬ ∀ (now : Day) (bm : Nat) (p q : WfPlan), autoClose now bm p = .ok q →
      ∀ (i : Id) (e : Entity), q.val.store.get i = some e →
        ∀ (r : Region), docRegion q.val e.val.live.doc = some r → ¬ Closed r now := by
  intro hall
  have hw := the_stale_catch_up_leaves_only_settled_and_recurring_lines
  unfold staleCaughtUp at hw
  cases h : autoClose staleNow 50 stalePlan with
  | error x => rw [h] at hw; simp at hw
  | ok q =>
    rw [h] at hw
    simp only [Option.some.injEq] at hw
    have hm : "t1".toList ∈ closedLiveIds staleNow q := by rw [hw]; decide
    obtain ⟨e, r, hg, hr, hc⟩ := mem_closedLiveIds hm
    exact hall staleNow 50 stalePlan q h _ e hg r hr hc

/-- An `autoClose` refusal, if the request loads and the call refuses. -/
def autoCloseRefusal (docs : List ReqDoc) : Option KErr :=
  (loadedPlan? docs).bind (fun p =>
    match autoClose staleNow 50 p with
    | .ok _    => none
    | .error k => some k)

set_option maxRecDepth 40000 in
/-- **The check bites, on loaded plans.**  The stale tree without the live week
has nowhere to file its day leftovers — `noTarget`, at the day grain; without
the open month, nowhere to file its week records — `noTarget`, at the week grain,
after the day close succeeded.  Either way the call refuses whole
(`autoClose_refuses_what_a_grain_refuses`): no grain is run and reported done
while another strands its lines. -/
theorem the_stale_catch_up_refusals_are_named :
    autoCloseRefusal (staleWitness.filter (fun d => d.path != "week/2026-W37.md")) =
        some .noTarget ∧
      autoCloseRefusal (staleWitness.filter (fun d => d.path != "month/2026-09.md")) =
        some .noTarget := by
  decide

/-! ## What a close reports, and `now` on the wire (stage-4 step 5)

The owner's D3 on the wire: `ok` carries `report` beside `docs`, and a close's
entries name each line it touched (Report.lean).  `now` and `blockMin` enter
the request (`ReqClock`), and the two close ops read them.  Both directions
(AGENTS §5.8), on the code `run` calls: the clock and the close ops are read,
and a missing or malformed value is refused by name; the report is populated on
three loaded plans, one per grain, and a refusal carries none. -/

/-- **The clock reads.** -/
theorem the_clock_reads_now_and_blockMin :
    (parseClock (.obj [("now".toList, .str "2026-09-12".toList), ("blockMin".toList, .num 50)])).map
      (fun c => (c.now, c.blockMin.map Subtype.val)) = .ok (some (Cal.toDay ⟨2026, 9, 12⟩), some 50) :=
  rfl

/-- **The clock bites, by name.**  Absent is absent — a request with no clock
still reads — but a present value is never ignored: 30 February, an unpadded
month, a number, and `null` are `badNow`; `0` and a string are `badBlockMin`;
a `now` carried twice is `duplicateKey now`. -/
theorem the_clock_refuses_a_malformed_value_by_name :
    (parseClock (.obj [])).map (fun c => (c.now, c.blockMin.map Subtype.val)) = .ok (none, none) ∧
    (parseClock (.obj [("now".toList, .str "2026-02-30".toList)])).map (fun c => c.now) = .error "badNow" ∧
    (parseClock (.obj [("now".toList, .str "2026-9-12".toList)])).map (fun c => c.now) = .error "badNow" ∧
    (parseClock (.obj [("now".toList, .num 739870)])).map (fun c => c.now) = .error "badNow" ∧
    (parseClock (.obj [("now".toList, .null)])).map (fun c => c.now) = .error "badNow" ∧
    (parseClock (.obj [("blockMin".toList, .num 0)])).map (fun c => c.now) = .error "badBlockMin" ∧
    (parseClock (.obj [("blockMin".toList, .str "50".toList)])).map (fun c => c.now) = .error "badBlockMin" ∧
    (parseClock (.obj [("now".toList, .str "2026-09-12".toList),
        ("now".toList, .str "2026-09-13".toList)])).map (fun c => c.now) = .error "duplicateKey now" :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def clockAbsent : ReqClock := ⟨none, none⟩
def clockNowOnly : ReqClock := ⟨some closeNow, none⟩
def blockMin50 : BlockMin := ⟨50, by decide⟩
def clockBoth : ReqClock := ⟨some closeNow, some blockMin50⟩

/-- **The close ops read the clock, and never invent it.**  Without `now` a
close and an autoClose are `nowAbsent`; with `now` and no `blockMin`,
`blockMinAbsent`; a grain out of range is refused as a document's is; with both,
the commands carry the request's own instant and block length; and an op that
reads no clock parses without one. -/
theorem parseCmdAt_reads_the_close_ops_and_refuses_without_the_clock :
    parseCmdAt clockAbsent (.obj [("op".toList, .str "close".toList), ("grain".toList, .num 1)])
      = .error "nowAbsent" ∧
    parseCmdAt clockNowOnly (.obj [("op".toList, .str "close".toList), ("grain".toList, .num 1)])
      = .error "blockMinAbsent" ∧
    parseCmdAt clockAbsent (.obj [("op".toList, .str "autoClose".toList)]) = .error "nowAbsent" ∧
    parseCmdAt clockBoth (.obj [("op".toList, .str "close".toList), ("grain".toList, .num 3)])
      = .error "grain 3 out of range (0..2)" ∧
    parseCmdAt clockBoth (.obj [("op".toList, .str "close".toList), ("grain".toList, .num 1)])
      = .ok (.close week closeNow blockMin50) ∧
    parseCmdAt clockBoth (.obj [("op".toList, .str "autoClose".toList)])
      = .ok (.autoClose closeNow blockMin50) ∧
    parseCmdAt clockAbsent (.obj [("op".toList, .str "drop".toList), ("id".toList, .str "a".toList)])
      = .ok (.drop "a".toList) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Every other op is `parseCmd`'s**, whatever the clock — so each parse
result stated about `parseCmd` is one about what `run` reads. -/
theorem parseCmdAt_is_parseCmd (c : ReqClock) (j : JVal) (op : List Char)
    (h1 : getStr j "op" = .ok op) (h2 : String.ofList op ≠ "close")
    (h3 : String.ofList op ≠ "autoClose") : parseCmdAt c j = parseCmd j := by
  unfold parseCmdAt
  simp only [h1, bind, Except.bind]

/-- **On the request, before anything loads**: a close in a request that omits
`now` is `nowAbsent`, and a malformed `now` is `badNow` even when no command
reads it; a request whose clock is whole reports under `ok`. -/
theorem run_names_the_clock_refusals :
    run (.obj [("docs".toList, .arr []), ("cmds".toList,
        .arr [.obj [("op".toList, .str "close".toList), ("grain".toList, .num 1)]])])
      = .error (jsonErr "nowAbsent") ∧
    run (.obj [("docs".toList, .arr []), ("now".toList, .str "2026-02-30".toList),
        ("cmds".toList, .arr [])])
      = .error (jsonErr "badNow") ∧
    run (.obj [("docs".toList, .arr []), ("now".toList, .str "2026-09-07".toList),
        ("blockMin".toList, .num 50), ("cmds".toList, .arr [.obj [("op".toList, .str "autoClose".toList)]])])
      = .ok (jone "ok" (.obj [("docs".toList, .arr []), ("report".toList, reportJson Report.empty)])) :=
  ⟨rfl, rfl, rfl⟩

/-- **Rule 1: a host that gets `err` gets no report.**  A refused request's
response is the refusal, and nothing beside it. -/
theorem runPlan_refusal_carries_no_report (p : WfPlan) (cs : List ReqCmd) (k : KErr)
    (h : applyAllR cs p = .error k) :
    runPlan p cs = .error (jone "err" (jone "kernel" (.str (kerrName k).toList))) := by
  unfold runPlan
  simp only [h, bind, Except.bind]
  rfl

/-- A close's report on a loaded plan, if it loads and the close succeeds. -/
def closedReport (g : Grain) (docs : List ReqDoc) : Option (List CloseEntry) :=
  (loadedPlan? docs).bind (fun p =>
    match closeR g closeNow blockMin50 p with
    | .ok qr    => some qr.2.closes
    | .error _ => none)

set_option maxRecDepth 40000 in
/-- **The report is populated on a real close — the week row.**  On
`the_week_close_copies_carries_and_leaves_the_rest`'s plan: the wall still
ahead is `carry` from `week/2026-W36.md` (document 0) into the live week
(document 1), unstamped, 2 h; the open line is `copy` into the month
(document 2), stamped `W36`, 6 blocks at 50 minutes.  The done and recurring
lines are not named.  The entries come in fold order, which is source order
since gap 59's fix: `^m2` (rank 1) before `^x1` (rank 3). -/
theorem the_week_close_reports_each_line :
    closedReport week closeWeekWitness = some
      [⟨"m2".toList, week, .copy, 0, 2, some (.week 36), some (Arith.posOfNat 300)⟩,
       ⟨"x1".toList, week, .carry, 0, 1, none, some (Arith.posOfNat 120)⟩] := by
  decide

set_option maxRecDepth 40000 in
/-- **The day row**: the pinned `[>]` is `moveReopening` into 2026-W37
(document 2, the week of *now*, D1), stamped `D04`, 20 minutes. -/
theorem the_day_close_reports_each_line :
    closedReport day closeDayWitness = some
      [⟨"p1".toList, day, .moveReopening, 0, 2, some (.day 4), some (Arith.posOfNat 20)⟩] := by
  decide

set_option maxRecDepth 40000 in
/-- **The month row**: the `[-]` record and the open outcome are `move`,
unstamped; the record reports `est:3b` as 150 minutes, and the outcome, which
carries no estimate, reports `null` — never `0`.  Source order (gap 59): the
outcome at rank 1 before the record at rank 4. -/
theorem the_month_close_reports_each_line :
    closedReport month closeMonthWitness = some
      [⟨"O7".toList, month, .move, 0, 1, none, none⟩,
       ⟨"m9".toList, month, .move, 0, 1, none, some (Arith.posOfNat 150)⟩] := by
  decide

/-- **An entry on the wire, byte for byte, in build order**: minutes as an
integer numerator and denominator, never a quotient. -/
theorem a_close_entry_emits_in_build_order :
    jemit (closeEntryJson ⟨"m2".toList, week, .copy, 0, 2, some (.week 36), some (Arith.posOfNat 300)⟩)
      = "{\"id\":\"m2\",\"grain\":1,\"did\":\"copy\",\"from\":0,\"to\":2,\"stamp\":\"W36\",\"min\":{\"num\":300,\"den\":1}}".toList ∧
    jemit (closeEntryJson ⟨"O7".toList, month, .move, 0, 1, none, none⟩)
      = "{\"id\":\"O7\",\"grain\":2,\"did\":\"move\",\"from\":0,\"to\":1,\"stamp\":null,\"min\":null}".toList := by
  decide

/-! ## Three stage-4 goals stated stronger than §6.3, refuted (stage-4 step 6)

`close_leaves_no_live_line_in_a_closed_region`, `close_never_demotes_a_wall` and
`close_writes_every_estimate_through_demoteEst` each forbid something §6.3
requires a close to do, so each is refuted here by its negation, quantifier for
quantifier, on the loaded week witness of step 2 (`closeWeekWitness`, closed at
Monday 2026-09-07).  One witness, three sightings:

* `^t1`, a `[x]` line of 2026-W36, stays in that closed week — §6.3 leaves
  settled lines where they are (and `^r1`, a recurring one, beside it);
* `^x1`, a wall still ahead, is carried out of 2026-W36 into 2026-W37 — F4's
  carry, which changes its `live` and so its `Core`;
* `^m2`'s record is written with `demoted:W36` and no `est:` key — a line
  `demoteEst` never writes, since `setEst` always leaves one (`hasEst_setEst`).

The narrowed laws that do hold sit beside each goal's old statement in
`Close.lean`: `close_leaves_no_line_it_would_take`,
`close_never_demotes_a_wall_but_may_carry_it`,
`close_rewrites_a_line_only_by_stamping_or_merging_it` and
`close_reads_every_remaining_estimate_through_demoteEst` (the last two restated at
README gap 53, and again at goal B3's repair as
`close_rewrites_a_line_only_by_stamping_merging_or_folding_it` and
`close_reads_every_remaining_estimate_through_demoteEst_and_the_fold`).  Probed under an 8 GB cap first (AGENTS
§5.10a): the three observations decide in about 4 s at a 1.3 GB peak, imports
included. -/

theorem the_close_week_witness_loads : loadsOk closeWeekWitness = true := by decide

/-- The loaded week witness.  Total by `the_close_week_witness_loads`: the error
branch is refuted, not defaulted. -/
def closeWeekPlan : WfPlan :=
  match h : loadPlan closeWeekWitness with
  | .ok p => p
  | .error _ => absurd the_close_week_witness_loads (by simp [loadsOk, h])

/-- The ids whose record sits in a file of grain `g` whose region is closed at
`now` — `closedLiveIds` with the goal's `r.grain = g` added. -/
def closedLiveIdsOfGrain (g : Grain) (now : Day) (q : WfPlan) : List Id :=
  q.val.store.dom.filter (fun i =>
    match q.val.store.get i with
    | none   => false
    | some e =>
      match docRegion q.val e.val.live.doc with
      | none   => false
      | some r => r.grain == g && decide (Closed r now))

/-- The week witness after `close week closeNow`, observed. -/
def weekClosed {α : Type} (obs : WfPlan → α) : Option α :=
  match close week closeNow 50 closeWeekPlan with
  | .ok q    => some (obs q)
  | .error _ => none

/-- One id's entity before and after the week close, observed together. -/
def beforeAfterWeekClose {α : Type} (i : Id) (obs : Entity → Entity → α) (q : WfPlan) : Option α :=
  match closeWeekPlan.val.store.get i, q.val.store.get i with
  | some e, some f => some (obs e f)
  | _, _ => none

/-- A line of `at:` shape — a wall. -/
def isIntervalLine (e : Entity) : Bool :=
  match e.val.shape with
  | .interval _ _ => true
  | _ => false

set_option maxRecDepth 40000 in
/-- After the week close, the recurring `^r1` and the done `^t1` are still in
2026-W36, a closed week. -/
theorem the_week_close_leaves_r1_and_t1_in_the_closed_week :
    weekClosed (closedLiveIdsOfGrain week closeNow) =
      some ["r1".toList, "t1".toList] := by decide
set_option maxRecDepth 40000 in
/-- `^x1` is an `at:` line in document 0 (2026-W36) before the close and in
document 1 (2026-W37) after it. -/
theorem the_week_close_carries_the_wall_x1_to_another_file :
    weekClosed (beforeAfterWeekClose "x1".toList
      (fun e f => (isIntervalLine e, e.val.live.doc, f.val.live.doc))) =
      some (some (true, 0, 1)) := by decide
set_option maxRecDepth 40000 in
/-- `^m2`'s line after the close differs from its line before (the stamp), and
carries no `est:` key. -/
theorem the_week_close_stamps_m2_and_writes_no_estimate :
    weekClosed (beforeAfterWeekClose "m2".toList
      (fun e f => (decide (f.val.line = e.val.line), hasEst f.val.line))) =
      some (some (false, false)) := by decide

theorem mem_closedLiveIdsOfGrain {g : Grain} {now : Day} {q : WfPlan} {i : Id}
    (h : i ∈ closedLiveIdsOfGrain g now q) :
    ∃ e r, q.val.store.get i = some e ∧ docRegion q.val e.val.live.doc = some r ∧
      r.grain = g ∧ Closed r now := by
  unfold closedLiveIdsOfGrain at h
  have hf := (List.mem_filter.1 h).2
  revert hf
  cases hg : q.val.store.get i with
  | none => simp
  | some e =>
    cases hr : docRegion q.val e.val.live.doc with
    | none => simp [hr]
    | some r =>
      simp only [hr, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact fun ⟨hgr, hc⟩ => ⟨e, r, rfl, hr, hgr, hc⟩

/-- **L18 at plan level (P\*), refuted — discharged from `Goals.lean` by
refute-and-rename.**  The negation of `close_leaves_no_live_line_in_a_closed_region`,
quantifier for quantifier.  §6.3 leaves settled, recurring and wall lines in a
closed file, so a close that succeeds can leave a live line in a closed region of
its own grain: `^t1`, `[x]` in 2026-W36.  What holds is
`close_leaves_no_line_it_would_take` (Close.lean): no line the close would take
survives it. -/
theorem close_leaves_live_lines_in_a_closed_region :
    ¬ ∀ (g : Grain) (now : Day) (bm : Nat) (p q : WfPlan), close g now bm p = .ok q →
      ∀ (i : Id) (e : Entity), q.val.store.get i = some e →
        ∀ (r : Region), docRegion q.val e.val.live.doc = some r → r.grain = g →
          ¬ Closed r now := by
  intro hall
  have hw := the_week_close_leaves_r1_and_t1_in_the_closed_week
  unfold weekClosed at hw
  cases h : close week closeNow 50 closeWeekPlan with
  | error x => rw [h] at hw; simp at hw
  | ok q =>
    rw [h] at hw
    simp only [Option.some.injEq] at hw
    have hm : "t1".toList ∈ closedLiveIdsOfGrain week closeNow q := by rw [hw]; decide
    obtain ⟨e, r, hg, hr, hgr, hc⟩ := mem_closedLiveIdsOfGrain hm
    exact hall week closeNow 50 closeWeekPlan q h _ e hg r hr hgr hc

/-- **F4 (P\*), refuted — discharged from `Goals.lean` by refute-and-rename.**
The negation of `close_never_demotes_a_wall`, quantifier for quantifier.  Its
conclusion `f.val = e.val` forbids the carry §6.3's exemptions require (and the
rank shift a landing performs): `^x1`, a wall still ahead, leaves 2026-W36 for
2026-W37.  What holds is `close_never_demotes_a_wall_but_may_carry_it`
(Close.lean): a wall or recurring line keeps its box, bytes and tombstone, and
only its file may change. -/
theorem close_does_not_leave_every_wall_as_it_was :
    ¬ ∀ (g : Grain) (now : Day) (bm : Nat) (p q : WfPlan), close g now bm p = .ok q →
      ∀ (i : Id) (e f : Entity), p.val.store.get i = some e → q.val.store.get i = some f →
        (e.val.recur ≠ Field.Recur.none ∨ ∃ a b : Field.DT, e.val.shape = Field.Shape.interval a b) →
        f.val = e.val := by
  intro hall
  have hw := the_week_close_carries_the_wall_x1_to_another_file
  unfold weekClosed beforeAfterWeekClose at hw
  cases h : close week closeNow 50 closeWeekPlan with
  | error x => rw [h] at hw; simp at hw
  | ok q =>
    rw [h] at hw
    simp only [Option.some.injEq] at hw
    cases he : closeWeekPlan.val.store.get "x1".toList with
    | none => rw [he] at hw; simp at hw
    | some e =>
      cases hf : q.val.store.get "x1".toList with
      | none => rw [he, hf] at hw; simp at hw
      | some f =>
        rw [he, hf] at hw
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨hwall, he0, hf1⟩ := hw
        have hsh : ∃ a b : Field.DT, e.val.shape = Field.Shape.interval a b := by
          unfold isIntervalLine at hwall
          split at hwall
          · rename_i a b hs; exact ⟨a, b, hs⟩
          · exact absurd hwall (by simp)
        have heq := congrArg (fun c => c.live.doc) (hall week closeNow 50 closeWeekPlan q h _ e f he hf (Or.inr hsh))
        simp only [he0, hf1] at heq
        exact absurd heq (by decide)

/-- **B1–B3 (P\*), refuted — discharged from `Goals.lean` by refute-and-rename.**
The negation of `close_writes_every_estimate_through_demoteEst`, quantifier for
quantifier.  It equates the whole line, and §6.3's `demoted:` stamp is not
`demoteEst`'s to write: `^m2`'s stamped record is neither its old line
(`userSet = true`) nor any line with an `est:` key (`userSet = false`, by
`hasEst_setEst`), at a 50-minute block.  What holds is
`close_rewrites_a_line_only_by_stamping_or_merging_it` and, for the estimate itself,
`close_reads_every_remaining_estimate_through_demoteEst` (Close.lean; restated at goal
B3's repair with the child fold, `…_merging_or_folding_it` and `…_and_the_fold`). -/
theorem close_writes_a_line_demoteEst_does_not :
    ¬ ∀ (g : Grain) (now : Day) (bm : Nat) (p q : WfPlan), close g now bm p = .ok q →
      ∀ (i : Id) (e f : Entity), p.val.store.get i = some e → q.val.store.get i = some f →
        ∃ (userSet : Bool) (rec : Nat), f.val.line = (demoteEst bm userSet rec e).val.line := by
  intro hall
  have hw := the_week_close_stamps_m2_and_writes_no_estimate
  unfold weekClosed beforeAfterWeekClose at hw
  cases h : close week closeNow 50 closeWeekPlan with
  | error x => rw [h] at hw; simp at hw
  | ok q =>
    rw [h] at hw
    simp only [Option.some.injEq] at hw
    cases he : closeWeekPlan.val.store.get "m2".toList with
    | none => rw [he] at hw; simp at hw
    | some e =>
      cases hf : q.val.store.get "m2".toList with
      | none => rw [he, hf] at hw; simp at hw
      | some f =>
        rw [he, hf] at hw
        simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hw
        obtain ⟨hne, hnoest⟩ := hw
        obtain ⟨u, rec, hl⟩ := hall week closeNow 50 closeWeekPlan q h _ e f he hf
        cases u with
        | true => exact hne hl
        | false =>
          have : hasEst f.val.line = true := by
            rw [hl]; exact hasEst_setEst _ _
          rw [hnoest] at this
          exact Bool.noConfusion this

/-! ## Gap 59 on loaded plans: a close keeps source order (stage 4 step 8)

`close_keeps_source_order` (Close.lean) is the law; these are its sightings on
plans the loader built, one per landing the table names, each with **two** lines
landing in one place — the shape every earlier close witness lacked, which is
how the reversal went unwitnessed.  Before `closeCands` sorted, each of the first
three decided with the pair the other way round.  The fourth is why the law
carries its section hypothesis: a month close files each line under the heading
it stood under, and the destination orders its sections itself.  Probed under an
8 GB cap first (AGENTS §5.10a). -/

/-- Two open lines of the closed 2026-W36, and a month whose `# Demoted` is
followed by another section. -/
def closeOrderWeekWitness : List ReqDoc :=
  [⟨"week/2026-W36.md", some closeW36,
     ["# Tasks".toList, "- [ ] 2 1b Draft the outline ^m1".toList,
      "- [ ] 3 2b Rollback path passes tests ^m2".toList]⟩,
   ⟨"week/2026-W37.md", some closeW37, ["# Tasks".toList]⟩,
   ⟨"month/2026-09.md", some closeM09,
     ["# Outcomes".toList, "# Demoted".toList, "# Notes".toList]⟩]

set_option maxRecDepth 40000 in
/-- **The week row keeps source order in `# Demoted`.**  `^m1` stood above `^m2`
in 2026-W36; its record lands above `^m2`'s at the end of the month's
`# Demoted`, both ahead of `# Notes` (gap 59: the fold used to land `^m2`
first). -/
theorem the_week_close_keeps_source_order_in_demoted :
    closedFileLines week closeOrderWeekWitness = some
      [["# Tasks".toList, "- [-] 2 1b Draft the outline ^m1".toList,
        "- [-] 3 2b Rollback path passes tests ^m2".toList],
       ["# Tasks".toList],
       ["# Outcomes".toList, "# Demoted".toList,
        "- [-] 2 1b Draft the outline demoted:W36 ^m1".toList,
        "- [-] 3 2b Rollback path passes tests demoted:W36 ^m2".toList, "# Notes".toList]] := by
  decide

/-- Two open outcomes of the closed August, and September's `# Outcomes` with a
line already in it. -/
def closeOrderMonthWitness : List ReqDoc :=
  [⟨"month/2026-08.md", some closeM08,
     ["# Outcomes".toList, "- [ ] 5 !1 First outcome ^O6".toList,
      "- [ ] 3 !2 Second outcome ^O7".toList, "# Demoted".toList]⟩,
   ⟨"month/2026-09.md", some closeM09,
     ["# Outcomes".toList, "- [ ] 5 !1 Lean through ch.8 ^O1".toList, "# Demoted".toList]⟩]

set_option maxRecDepth 40000 in
/-- **The month row keeps source order in the section a line came from.**  Both
outcomes land after the line September already has, in August's order, ahead of
`# Demoted` (gap 59: `^O7` used to land above `^O6`). -/
theorem the_month_close_keeps_source_order_in_its_section :
    closedFileLines month closeOrderMonthWitness = some
      [["# Outcomes".toList, "# Demoted".toList],
       ["# Outcomes".toList, "- [ ] 5 !1 Lean through ch.8 ^O1".toList,
        "- [ ] 5 !1 First outcome ^O6".toList, "- [ ] 3 !2 Second outcome ^O7".toList,
        "# Demoted".toList]] := by
  decide

/-- Two pinned `[>]` lines of Friday 2026-09-04, closed on the Monday after. -/
def closeOrderDayWitness : List ReqDoc :=
  [⟨"day/2026-09-04.md", some ⟨day, Cal.toDay ⟨2026, 9, 4⟩⟩,
     ["# Pinned".toList, "- [>] 2 20m Call the bank ^p1".toList,
      "- [>] 1 10m Book the room ^p2".toList]⟩,
   ⟨"week/2026-W37.md", some closeW37,
     ["# Tasks".toList, "- [ ] 3 1b Review the drafts ^t5".toList]⟩]

set_option maxRecDepth 40000 in
/-- **The day row keeps source order at the end of the week.**  `^p1` then `^p2`,
after the line the week already has (gap 59: `^p2` used to land first). -/
theorem the_day_close_keeps_source_order_at_the_end_of_the_week :
    closedFileLines day closeOrderDayWitness = some
      [["# Pinned".toList],
       ["# Tasks".toList, "- [ ] 3 1b Review the drafts ^t5".toList,
        "- [ ] 2 20m Call the bank demoted:D04 ^p1".toList,
        "- [ ] 1 10m Book the room demoted:D04 ^p2".toList]] := by
  decide

/-- August's two outcomes under two different headings, and a September that
orders those headings the other way. -/
def closeOrderSectionsWitness : List ReqDoc :=
  [⟨"month/2026-08.md", some closeM08,
     ["# Reading".toList, "- [ ] 2 !2 Read the paper ^O6".toList,
      "# Writing".toList, "- [ ] 3 !2 Draft the essay ^O7".toList]⟩,
   ⟨"month/2026-09.md", some closeM09, ["# Writing".toList, "# Reading".toList]⟩]

set_option maxRecDepth 40000 in
/-- **Why `close_keeps_source_order` asks for one heading at the month grain.**
`^O6` stood above `^O7` in August, under `# Reading`; it lands below `^O7` in
September, because September's `# Reading` follows its `# Writing`.  §6.3's
"each into the section it came from" decides this, not the fold's order, so the
law without the section hypothesis is false and stays unstated. -/
theorem the_month_close_orders_lines_by_the_destination_sections :
    closedFileLines month closeOrderSectionsWitness = some
      [["# Reading".toList, "# Writing".toList],
       ["# Writing".toList, "- [ ] 3 !2 Draft the essay ^O7".toList,
        "# Reading".toList, "- [ ] 2 !2 Read the paper ^O6".toList]] := by
  decide

/-- The report names two lines of one file in source order too: the fold order
is the report order (`closeReport_ids`). -/
theorem the_week_close_reports_in_source_order :
    (closedReport week closeOrderWeekWitness).map (fun es => es.map CloseEntry.id) =
      some ["m1".toList, "m2".toList] := by
  decide

/-! ## Gap 20's remainder: the `demote` verb files into `# Demoted` (stage 4 step 9)

`applyCmd (.demote …)` now lands through `landAt` at `demoteSpot` — the week
close's `Landing.demotedSection` spot, with the close's shift — instead of at
`freshRank`.  Where no shift happens the verb is exactly the stage-3 command
(`demote_verb_is_cmdDemote_at_freshRank_without_a_shift_or_a_record`, which since
README gap 53 also asks that the item have no standing record), so every law about
`cmdDemote` at `freshRank` still describes it there; where the month's `# Demoted`
is followed by another section the record now lands inside it.  The witness
below decides two demotes landing in the order they ran; that is a sighting, not
a law — no theorem here quantifies over command sequences.  Probed under an 8 GB
cap first (AGENTS §5.10a). -/

theorem WfPlan.mapAt_congr {p : WfPlan} {i : Id} {F G : Entity → Except KErr Entity}
    (h : ∀ e, p.val.store.get i = some e → F e = G e) : p.mapAt i F = p.mapAt i G := by
  unfold WfPlan.mapAt
  split
  · rfl
  · rename_i e he
    rw [h e he]

/-- Where no shift happens and the item has no standing record, the verb is the
stage-3 command at `freshRank`.  (Restates
`demote_verb_is_cmdDemote_at_freshRank_without_a_shift`: since README gap 53 the
verb's transform is `refile`, which merges an item that has a `# Demoted` record
where `cmdDemote`'s `demote` refuses it, so the two agree only on items with
none — `refile_of_no_record`.) -/
theorem demote_verb_is_cmdDemote_at_freshRank_without_a_shift_or_a_record (p : WfPlan) (i : Id)
    (n : Nat) (st : Field.Stamp) (dd : Dest p.val) (hrd : resolveDest p.val n = .ok dd)
    (h : demoteSpot p.val dd.ix = none)
    (hrec : ∀ e, p.val.store.get i = some e → e.val.archive = none) :
    applyCmd (.demote i n st) p = cmdDemote i (freshRank p.val dd.ix) st p dd := by
  have hs : (p.val.store.get i).any (hasAStrayTomb p.val) = false := by
    cases hg : p.val.store.get i with
    | none => rfl
    | some e => simp [hasAStrayTomb, hrec e hg]
  simp only [applyCmd, hrd, h, landAt, cmdDemote, Dest.site, endRank_is_freshRank, hs, guardStray_false]
  exact WfPlan.mapAt_congr (fun e he => refile_of_no_record _ _ e (hrec e he))

/-- Each file's lines after running `cs` on a loaded request, if both succeed. -/
def cmdsFileLines (cs : List ReqCmd) (docs : List ReqDoc) : Option (List (List (List Char))) :=
  (loadedPlan? docs).bind (fun p => closeResultLines (applyAll cs p))

/-- Two open lines of the live 2026-W37, and a September whose `# Demoted` is
followed by `# Notes`. -/
def demoteSectionWitness : List ReqDoc :=
  [⟨"week/2026-W37.md", some closeW37,
     ["# Tasks".toList, "- [ ] 2 1b Draft the outline ^m1".toList,
      "- [ ] 3 2b Rollback path passes tests ^m2".toList]⟩,
   ⟨"month/2026-09.md", some closeM09,
     ["# Outcomes".toList, "# Demoted".toList, "# Notes".toList]⟩]

set_option maxRecDepth 40000 in
/-- **§6.3's "copies it into `month/<current>#Demoted`", by the verb.**  Both
records land at the end of `# Demoted`, ahead of `# Notes`, in the order they
were demoted; before this step both landed after `# Notes`, under the wrong
heading. -/
theorem the_demote_verb_files_into_demoted_ahead_of_the_next_section :
    cmdsFileLines [.demote "m1".toList 1 (.week 37), .demote "m2".toList 1 (.week 37)]
        demoteSectionWitness = some
      [["# Tasks".toList, "- [-] 2 1b Draft the outline ^m1".toList,
        "- [-] 3 2b Rollback path passes tests ^m2".toList],
       ["# Outcomes".toList, "# Demoted".toList,
        "- [-] 2 1b Draft the outline demoted:W37 ^m1".toList,
        "- [-] 3 2b Rollback path passes tests demoted:W37 ^m2".toList, "# Notes".toList]] := by
  decide

/-- A September with no `# Demoted`. -/
def demoteNoSectionWitness : List ReqDoc :=
  [⟨"week/2026-W37.md", some closeW37,
     ["# Tasks".toList, "- [ ] 2 1b Draft the outline ^m1".toList]⟩,
   ⟨"month/2026-09.md", some closeM09, ["# Outcomes".toList]⟩]

set_option maxRecDepth 40000 in
/-- **The one difference from the close, decided (README gap 60).**  With no
`# Demoted` in the destination the week close refuses `noSection`; the verb lands
the record at the end of the file, as it did at stage 3. -/
theorem the_demote_verb_lands_at_the_end_of_a_month_without_demoted :
    cmdsFileLines [.demote "m1".toList 1 (.week 37)] demoteNoSectionWitness = some
      [["# Tasks".toList, "- [-] 2 1b Draft the outline ^m1".toList],
       ["# Outcomes".toList, "- [-] 2 1b Draft the outline demoted:W37 ^m1".toList]] := by
  decide

/-! ## Gap 53: §4.3's pre-close pair closes, merged (stage-4 hardening step 2)

Until this step §4.3's own example week refused its week close: a `[ ]` line in the
week beside its `[-]` record under the month's `# Demoted` is one item with an open
live line and a standing tombstone, and the week row's `demote` answered
`alreadyDemoted`.  The copy is `refile` now (Cmd.lean), fork-point `demote_one`'s
merge with L15's floor, and the verb runs the same transform.  One witness, three
items, closed at Monday 2026-09-07:

* `^m2` owns an estimate (`6b`): its record keeps the line's bytes with the stamps
  merged — the record's `W37`, then this close's `W36` — and does not take the
  record's `est:3b` (`refile_respects_user`);
* `^m5` owns none: its record takes the standing record's `est:3b`, verbatim, and
  its stamps `W35,W36` (`refile_conserves`);
* `^m6`'s record already says `W36`, the week this close stamps: the merge writes
  it once (`mergeStamps_spec`), not `W36,W36`.

Probed under an 8 GB cap first (AGENTS §5.10a): the six decisions below take 8.5 s
at a 2.0 GB peak, imports included. -/

/-- 2026-W36 with three open lines, each with a `[-]` record already standing in
September's `# Demoted`, below the outcome `^O2` two of them name (D6). -/
def closeMergeWitness : List ReqDoc :=
  [⟨"week/2026-W36.md", some closeW36,
     ["# Milestones".toList,
      "- [ ] 4 6b Rollback path passes tests   @O2 ^m2".toList,
      "- [ ] 4 Write the rollback notes @O2 ^m5".toList,
      "- [ ] 3 1b Tidy the fixtures ^m6".toList]⟩,
   ⟨"month/2026-09.md", some closeM09,
     ["# Outcomes".toList, "- [ ] 4 !1 Soundcode: end-to-end demo runs             ^O2".toList, "# Demoted".toList,
      "- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2".toList,
      "- [-] 4 Write the rollback notes @O2 est:3b demoted:W35 ^m5".toList,
      "- [-] 3 1b Tidy the fixtures demoted:W36 ^m6".toList]⟩]

set_option maxRecDepth 40000 in
/-- **§6.3's week row over §4.3's pre-close pair, on a loaded plan.**  Each open
line stays behind as a `[-]` tombstone in its own bytes; each item's standing record
is gone from its old place and its merged record lands at the end of `# Demoted`,
in source order — one record per item. -/
theorem the_week_close_merges_each_standing_record :
    closedFileLines week closeMergeWitness = some
      [["# Milestones".toList, "- [-] 4 6b Rollback path passes tests   @O2 ^m2".toList,
        "- [-] 4 Write the rollback notes @O2 ^m5".toList, "- [-] 3 1b Tidy the fixtures ^m6".toList],
       ["# Outcomes".toList, "- [ ] 4 !1 Soundcode: end-to-end demo runs             ^O2".toList,
        "# Demoted".toList, "- [-] 4 6b Rollback path passes tests   @O2 demoted:W37,W36 ^m2".toList,
        "- [-] 4 Write the rollback notes @O2 est:3b demoted:W35,W36 ^m5".toList,
        "- [-] 3 1b Tidy the fixtures demoted:W36 ^m6".toList]] := by
  decide

set_option maxRecDepth 40000 in
/-- **The report names the merge.**  Each entry is `copyMerging`, stamped `W36`,
with its record's minutes afterwards at a 50-minute block: `6b` is 300, the carried
`est:3b` is 150, `1b` is 50. -/
theorem the_week_close_reports_each_merge :
    closedReport week closeMergeWitness = some
      [⟨"m2".toList, week, .copyMerging, 0, 1, some (.week 36), some (Arith.posOfNat 300)⟩,
       ⟨"m5".toList, week, .copyMerging, 0, 1, some (.week 36), some (Arith.posOfNat 150)⟩,
       ⟨"m6".toList, week, .copyMerging, 0, 1, some (.week 36), some (Arith.posOfNat 50)⟩] := by
  decide

set_option maxRecDepth 40000 in
/-- **The verb merges too.**  `tm demote ^m5` runs `refile`: the same record the
close writes, landing at the end of `# Demoted`, the old record gone. -/
theorem the_demote_verb_merges_into_a_standing_record :
    cmdsFileLines [.demote "m5".toList 1 (.week 36)] closeMergeWitness = some
      [["# Milestones".toList, "- [ ] 4 6b Rollback path passes tests   @O2 ^m2".toList,
        "- [-] 4 Write the rollback notes @O2 ^m5".toList, "- [ ] 3 1b Tidy the fixtures ^m6".toList],
       ["# Outcomes".toList, "- [ ] 4 !1 Soundcode: end-to-end demo runs             ^O2".toList,
        "# Demoted".toList, "- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2".toList,
        "- [-] 3 1b Tidy the fixtures demoted:W36 ^m6".toList,
        "- [-] 4 Write the rollback notes @O2 est:3b demoted:W35,W36 ^m5".toList]] := by
  decide

theorem the_close_merge_witness_loads : loadsOk closeMergeWitness = true := by decide

/-- The loaded merge witness.  Total by `the_close_merge_witness_loads`: the error
branch is refuted, not defaulted. -/
def closeMergePlan : WfPlan :=
  match h : loadPlan closeMergeWitness with
  | .ok p => p
  | .error _ => absurd the_close_merge_witness_loads (by simp [loadsOk, h])

set_option maxRecDepth 40000 in
/-- `^m5`'s remaining at a 50-minute block: nothing before the week close, the
standing record's 150 minutes after it. -/
theorem the_week_close_floors_m5_at_its_record :
    (match close week closeNow 50 closeMergePlan with
     | .ok q =>
       match closeMergePlan.val.store.get "m5".toList, q.val.store.get "m5".toList with
       | some e, some f => some (remainingOf 50 e.val.line, remainingOf 50 f.val.line)
       | _, _ => none
     | .error _ => none) = some (0, 150) := by
  decide

set_option maxRecDepth 40000 in
/-- `^m2`'s stamps across `autoClose`: none on its live line before, the record's
and the week's after. -/
theorem autoClose_merges_m2s_stamps :
    (match autoClose closeNow 50 closeMergePlan with
     | .ok q =>
       match closeMergePlan.val.store.get "m2".toList, q.val.store.get "m2".toList with
       | some e, some f => some (e.val.stamps, f.val.stamps)
       | _, _ => none
     | .error _ => none) = some ([], [.week 37, .week 36]) := by
  decide

/-- **`close_rewrites_a_line_only_by_stamping_it`, refuted since gap 53.**  Its
statement, quantifier for quantifier, is false once a close merges: `^m5`'s record
carries its standing record's `est:3b`, which no `demoted:` write adds.  What holds
is `close_rewrites_a_line_only_by_stamping_or_merging_it` (Close.lean; since goal B3's
repair `close_rewrites_a_line_only_by_stamping_merging_or_folding_it`). -/
theorem a_merged_record_is_rewritten_beyond_its_stamp :
    ¬ ∀ (g : Grain) (now : Day) (bm : Nat) (p q : WfPlan), close g now bm p = .ok q →
      ∀ (i : Id) (e f : Entity), p.val.store.get i = some e → q.val.store.get i = some f →
        f.val.line = e.val.line ∨ ∃ ss, f.val.line = Field.setDemoted ss e.val.line := by
  intro hall
  have hw := the_week_close_floors_m5_at_its_record
  cases h : close week closeNow 50 closeMergePlan with
  | error x => rw [h] at hw; simp at hw
  | ok q =>
    rw [h] at hw
    simp only at hw
    split at hw
    · rename_i e f he hf
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      rcases hall week closeNow 50 closeMergePlan q h _ e f he hf with hl | ⟨ss, hl⟩
      · rw [hl] at hw; omega
      · rw [hl, Field.remainingOf_setDemoted] at hw; omega
    · simp at hw

/-- **`close_keeps_every_remaining_estimate`, refuted since gap 53.**  `^m5`'s
remaining goes from nothing to its standing record's 150 minutes — L15's floor,
which a close that kept every estimate could not write.  What holds is
`close_reads_every_remaining_estimate_through_demoteEst` (Close.lean; since goal B3's
repair `close_reads_every_remaining_estimate_through_demoteEst_and_the_fold`). -/
theorem a_merged_record_changes_a_remaining_estimate :
    ¬ ∀ (g : Grain) (now : Day) (bm : Nat) (p q : WfPlan), close g now bm p = .ok q →
      ∀ (i : Id) (e f : Entity), p.val.store.get i = some e → q.val.store.get i = some f →
        ∀ bm, remainingOf bm f.val.line = remainingOf bm e.val.line := by
  intro hall
  have hw := the_week_close_floors_m5_at_its_record
  cases h : close week closeNow 50 closeMergePlan with
  | error x => rw [h] at hw; simp at hw
  | ok q =>
    rw [h] at hw
    simp only at hw
    split at hw
    · rename_i e f he hf
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      have := hall week closeNow 50 closeMergePlan q h _ e f he hf 50
      omega
    · simp at hw

/-- **`autoClose_stamps_each_line_at_most_once`, refuted since gap 53.**  `^m2`'s
live line carries no stamp and its merged record carries two — the record's `W37`
and the week's `W36` — which is neither "the same" nor "one appended".  What holds
is `autoClose_appends_at_most_one_stamp_or_merges_each_line` (Close.lean): keep, append one, or
merge. -/
theorem autoClose_merges_a_line_beyond_one_appended_stamp :
    ¬ ∀ (now : Day) (bm : Nat) (p q : WfPlan), autoClose now bm p = .ok q →
      ∀ (i : Id) (e f : Entity), p.val.store.get i = some e → q.val.store.get i = some f →
        f.val.stamps = e.val.stamps ∨ ∃ st, f.val.stamps = e.val.stamps ++ [st] := by
  intro hall
  have hw := autoClose_merges_m2s_stamps
  cases h : autoClose closeNow 50 closeMergePlan with
  | error x => rw [h] at hw; simp at hw
  | ok q =>
    rw [h] at hw
    simp only at hw
    split at hw
    · rename_i e f he hf
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨h1, h2⟩ := hw
      rcases hall closeNow 50 closeMergePlan q h _ e f he hf with hl | ⟨st, hl⟩
      · rw [h1, h2] at hl; exact absurd hl (by decide)
      · rw [h1, h2] at hl
        have := congrArg List.length hl
        simp at this
    · simp at hw

/-! ## Stage-4 hardening repair: a stray tombstone is refused, and the merge laws are not vacuous

`refile` merges into an item's tombstone and deletes its old placement, which is
right only when that tombstone is the item's `# Demoted` record.  Fork-point
`archived_record` reads a record only off a month file's `# Demoted`; a `[-]` line
left in an earlier week is an archive, and merging into it deleted a line from a
closed week file.  The close and the verb now refuse it, `alreadyDemoted`
(`closeOne_never_merges_into_a_stray_tomb`, Close.lean).  Below: the refusal on a
loaded plan at both entry points, the refutation of the laws that said no close
answers `alreadyDemoted`, the report's old stamp clause refuted, and the merge laws'
hypotheses instantiated together.  Probed under an 8 GB cap first (AGENTS §5.10a):
6.1 s at a 1.7 GB peak, imports included. -/

theorem the_stray_tomb_witness_loads : loadsOk closeStrayTombWitness = true := by decide

/-- The loaded stray-tombstone witness.  Total by `the_stray_tomb_witness_loads`. -/
def closeStrayTombPlan : WfPlan :=
  match h : loadPlan closeStrayTombWitness with
  | .ok p => p
  | .error _ => absurd the_stray_tomb_witness_loads (by simp [loadsOk, h])

set_option maxRecDepth 40000 in
/-- **The week close refuses a stray tombstone, and writes nothing.** -/
theorem a_stray_tomb_refuses_the_week_close :
    (match close week closeNow 50 closeStrayTombPlan with
     | .ok _ => none
     | .error k => some k) = some KErr.alreadyDemoted := by decide

set_option maxRecDepth 40000 in
/-- **So does the automatic close** — the one the binary runs. -/
theorem a_stray_tomb_refuses_autoClose :
    (match autoClose closeNow 50 closeStrayTombPlan with
     | .ok _ => none
     | .error k => some k) = some KErr.alreadyDemoted := by decide

set_option maxRecDepth 40000 in
/-- **And the verb**: `tm demote ^m4` into September refuses rather than deleting
the W35 line. -/
theorem the_demote_verb_refuses_a_stray_tomb :
    cmdsRefusal [.demote "m4".toList 2 (.week 36)] closeStrayTombPlan = some .alreadyDemoted := by
  decide

set_option maxRecDepth 40000 in
/-- `^m2` under the week close of the merge witness: no stamps before, `W37,W36`
after, and its report entry stamps `W36`. -/
theorem the_week_close_merges_m2s_stamps_and_reports_one :
    (match close week closeNow 50 closeMergePlan with
     | .ok q =>
       match closeMergePlan.val.store.get "m2".toList, q.val.store.get "m2".toList with
       | some e, some f => some (e.val.stamps, f.val.stamps,
           ((closeReport week closeNow blockMin50 closeMergePlan.val).find?
             (fun x => x.id == "m2".toList)).map CloseEntry.stamp)
       | _, _ => none
     | .error _ => none) = some ([], [.week 37, .week 36], some (some (.week 36))) := by
  decide

/-- What the merge laws assume of item `i`, read off a loaded plan `p` and a close's
result `q`: taken by the week row with a tombstone standing; whether the live line
owns an estimate; whether `refile` succeeds on it. -/
def mergeHypsAt (p q : WfPlan) (i : Id) : Option (Bool × Bool × Bool) :=
  match p.val.store.get i, q.val.store.get i with
  | some e, some _ =>
    some ((match closeAct week closeNow p.val e.val.skel with
           | .file _ => true
           | _       => false) && e.val.archive.isSome,
          ownsEstimate e.val.line,
          (match refile ⟨1, 99⟩ (.week 36) e with
           | .ok _    => true
           | .error _ => false))
  | _, _ => none

theorem mergeHypsAt_spec {p q : WfPlan} {i : Id} {b c : Bool}
    (h : mergeHypsAt p q i = some (true, b, c)) :
    ∃ e f r t, p.val.store.get i = some e ∧ q.val.store.get i = some f ∧
      closeAct week closeNow p.val e.val.skel = .file r ∧ e.val.archive = some t ∧
      ownsEstimate e.val.line = b ∧ (c = true → ∃ a, refile ⟨1, 99⟩ (.week 36) e = .ok a) := by
  unfold mergeHypsAt at h
  split at h
  · rename_i e f he hf
    simp only [Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true] at h
    obtain ⟨⟨hact, harch⟩, hb, hc⟩ := h
    split at hact
    · rename_i r hr
      cases ha : e.val.archive with
      | none => rw [ha] at harch; simp at harch
      | some t =>
        refine ⟨e, f, r, t, he, hf, hr, ha, hb, fun hc' => ?_⟩
        subst hc'
        split at hc
        · rename_i a ha'; exact ⟨a, ha'⟩
        · simp at hc
    · simp at hact
  · simp at h

set_option maxRecDepth 40000 in
/-- **The merge laws' hypotheses hold together on a loaded plan.**  Under the week
close of `closeMergeWitness`, `^m2` (owns `6b`) and `^m5` (owns none) are each taken
by the week row with a standing record, and `refile` succeeds on each. -/
theorem the_merge_hypotheses_hold_together :
    (match close week closeNow 50 closeMergePlan with
     | .ok q => [mergeHypsAt closeMergePlan q "m2".toList, mergeHypsAt closeMergePlan q "m5".toList]
     | .error _ => []) = [some (true, true, true), some (true, false, true)] := by
  decide

set_option maxRecDepth 40000 in
/-- The merge witness drops nothing: `^m2` and `^m5` name the outcome `^O2`, which the
week close does not file. -/
theorem the_merge_witness_drops_neither_record :
    dropsInto week closeNow closeMergePlan.val "m2".toList = none ∧
      dropsInto week closeNow closeMergePlan.val "m5".toList = none := by
  decide

/-- `close_week_merges_a_standing_record_it_does_not_drop`'s hypotheses are satisfiable
together, in both of its estimate branches.  (Restates
`close_week_merges_a_standing_record_is_not_vacuous` for the law B3's repair restated:
it gains the block length and the line not being dropped.) -/
theorem close_week_merges_a_standing_record_it_does_not_drop_is_not_vacuous (b : Bool) :
    ∃ (now : Day) (bm : Nat) (p q : WfPlan) (i : Id) (e f : Entity) (r : Region) (t : Tomb),
      close week now bm p = .ok q ∧ p.val.store.get i = some e ∧ q.val.store.get i = some f ∧
        closeAct week now p.val e.val.skel = .file r ∧ dropsInto week now p.val i = none ∧
        e.val.archive = some t ∧ ownsEstimate e.val.line = b := by
  have hw := the_merge_hypotheses_hold_together
  cases h : close week closeNow 50 closeMergePlan with
  | error k => rw [h] at hw; simp at hw
  | ok q =>
    rw [h] at hw
    simp only [List.cons.injEq] at hw
    obtain ⟨h2, h5, -⟩ := hw
    cases b
    · obtain ⟨e, f, r, t, he, hf, hr, ht, hb, -⟩ := mergeHypsAt_spec h5
      exact ⟨_, _, _, _, _, e, f, r, t, h, he, hf, hr, the_merge_witness_drops_neither_record.2, ht, hb⟩
    · obtain ⟨e, f, r, t, he, hf, hr, ht, hb, -⟩ := mergeHypsAt_spec h2
      exact ⟨_, _, _, _, _, e, f, r, t, h, he, hf, hr, the_merge_witness_drops_neither_record.1, ht, hb⟩

/-- `refile_conserves` (`b = false`) and `refile_respects_user` (`b = true`) have
satisfiable hypotheses: `^m5` and `^m2` of the loaded merge witness. -/
theorem refile_merge_laws_are_not_vacuous (b : Bool) :
    ∃ (t : Site) (st : Field.Stamp) (e a : Entity) (tb : Tomb),
      e.val.archive = some tb ∧ ownsEstimate e.val.line = b ∧ refile t st e = .ok a := by
  have hw := the_merge_hypotheses_hold_together
  cases h : close week closeNow 50 closeMergePlan with
  | error k => rw [h] at hw; simp at hw
  | ok q =>
    rw [h] at hw
    simp only [List.cons.injEq] at hw
    obtain ⟨h2, h5, -⟩ := hw
    cases b
    · obtain ⟨e, _, _, t, _, _, _, ht, hb, hc⟩ := mergeHypsAt_spec h5
      obtain ⟨a, ha⟩ := hc rfl
      exact ⟨_, _, e, a, t, ht, hb, ha⟩
    · obtain ⟨e, _, _, t, _, _, _, ht, hb, hc⟩ := mergeHypsAt_spec h2
      obtain ⟨a, ha⟩ := hc rfl
      exact ⟨_, _, e, a, t, ht, hb, ha⟩

/-- **`close_never_refuses_alreadyDemoted`, refuted** on a loaded plan. -/
theorem a_close_can_refuse_alreadyDemoted :
    ¬ ∀ (g : Grain) (now : Day) (bm : Nat) (p : WfPlan), close g now bm p ≠ .error .alreadyDemoted := by
  intro hall
  have hw := a_stray_tomb_refuses_the_week_close
  cases h : close week closeNow 50 closeStrayTombPlan with
  | ok q => rw [h] at hw; simp at hw
  | error k =>
    rw [h] at hw
    simp only [Option.some.injEq] at hw
    subst hw
    exact hall _ _ _ _ h

/-- **`closeReport_agrees_with_close`, as stated before gap 53, refuted.** -/
theorem closeReport_agrees_with_close_is_refuted_by_a_merge :
    ¬ ∀ (g : Grain) (now : Day) (bm : BlockMin) (p q : WfPlan), close g now bm.val p = .ok q →
      ∀ x ∈ closeReport g now bm p.val,
        x.grain = g ∧ ∃ e f, p.val.store.get x.id = some e ∧ q.val.store.get x.id = some f ∧
          e.val.live.doc = x.src ∧ f.val.live.doc = x.dst ∧
          f.val.stamps = e.val.stamps ++ x.stamp.toList ∧ x.minutes = estMinutes bm f.val.line := by
  intro hall
  have hw := the_week_close_merges_m2s_stamps_and_reports_one
  cases h : close week closeNow 50 closeMergePlan with
  | error k => rw [h] at hw; simp at hw
  | ok q =>
    rw [h] at hw
    simp only at hw
    split at hw
    · rename_i e f he hf
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨h1, h2, h3⟩ := hw
      obtain ⟨x, hx, hxs⟩ := Option.map_eq_some_iff.mp h3
      have hmem := List.mem_of_find?_eq_some hx
      have hid : x.id = "m2".toList := by simpa using List.find?_some hx
      obtain ⟨_, e', f', he', hf', _, _, hst, _⟩ := hall week closeNow blockMin50 closeMergePlan q h x hmem
      rw [hid, he] at he'
      rw [hid, hf] at hf'
      injection he' with he'
      injection hf' with hf'
      subst he' hf'
      rw [h1, h2, hxs] at hst
      exact absurd hst (by decide)
    · simp at hw

/-! ## Gap 55 closed: dated work routes itself (the owner's D7 and D8; stage 4 final, step 2)

§4.3's own week refused its automatic close on every command a week after `tm init
--example`: `^d1 due:2026-09-11T23:59` was filed into `# Demoted` like any open line,
and the month rule "an outcome carries no date" refused its record (`badHorizon`,
README gap 55).  The owner decided both halves on 2026-09-13: past due with
`persist`, the line moves to `backlog.md # Overdue` (D7); otherwise it is demoted
and keeps its date, which a `# Demoted` record may now carry (D8).  The witnesses
below are loaded plans, closed at Monday 2026-09-07 (`closeNow`) and, for §4.3's
literal files, at Monday 2026-09-14.

Probed under an 8 GB cap first (AGENTS §5.10a); the timings are in the README's
"Stage 4 final" step-2 block. -/

/-- 2026-W36 holding every dated case: `^d1` and `^d4` past due with `persist` (the
default; `^d4` a date-time), `^d2` not yet due, `^d3` past due with
`on-miss:expire`, `^x2` a wall that is over (`persist`), `^x3` a wall that is over
with `on-miss:next`; a backlog whose `# Overdue` is followed by another section, so
the landing shifts to make room. -/
def closeOverdueWitness : List ReqDoc :=
  [⟨"week/2026-W36.md", some closeW36,
     ["# Tasks".toList,
      "- [ ] 4 2b Pset two due:2026-09-04 ^d1".toList,
      "- [ ] 3 1b Essay draft due:2026-09-20 ^d2".toList,
      "- [ ] 2 1b Quiz prep due:2026-09-03 on-miss:expire ^d3".toList,
      "- [ ] 5 2h Lab session at:2026-09-02T10:00/12:00 ^x2".toList,
      "- [ ] 1 1h Reading group at:2026-09-01T15:00/16:00 on-miss:next ^x3".toList,
      "- [ ] 2 1b Pset three due:2026-09-05T23:59 ^d4".toList]⟩,
   ⟨"week/2026-W37.md", some closeW37, ["# Tasks".toList]⟩,
   ⟨"month/2026-09.md", some closeM09,
     ["# Outcomes".toList, "- [ ] 5 !1 Lean through ch.8 ^O1".toList, "# Demoted".toList]⟩,
   ⟨"backlog.md", none,
     ["# Untied".toList, "- [ ] 2 30m Insurance claim ^a1".toList, "# Overdue".toList,
      "# Later".toList, "- [ ] 1 1b Someday ^a2".toList]⟩]

set_option maxRecDepth 40000 in
/-- **§6.3's week row routes dated work, on a loaded plan.**  The three lines past
due with `persist` — two points and a wall that is over — leave the week file with
no `[-]` behind and land, as they were, unstamped and in source order, at the end
of the backlog's `# Overdue`, ahead of `# Later` (D7).  The not-yet-due `^d2` and
the past-due `on-miss:expire` `^d3` are demoted like any open line, their records
stamped `W36` and keeping their `due:` in `# Demoted` (D8).  The wall that is over
with `on-miss:next` stays where it is, as fork-point `close_week` leaves it. -/
theorem the_week_close_routes_dated_work_on_a_loaded_plan :
    closedFileLines week closeOverdueWitness = some
      [["# Tasks".toList, "- [-] 3 1b Essay draft due:2026-09-20 ^d2".toList,
        "- [-] 2 1b Quiz prep due:2026-09-03 on-miss:expire ^d3".toList,
        "- [ ] 1 1h Reading group at:2026-09-01T15:00/16:00 on-miss:next ^x3".toList],
       ["# Tasks".toList],
       ["# Outcomes".toList, "- [ ] 5 !1 Lean through ch.8 ^O1".toList, "# Demoted".toList,
        "- [-] 3 1b Essay draft due:2026-09-20 demoted:W36 ^d2".toList,
        "- [-] 2 1b Quiz prep due:2026-09-03 on-miss:expire demoted:W36 ^d3".toList],
       ["# Untied".toList, "- [ ] 2 30m Insurance claim ^a1".toList, "# Overdue".toList,
        "- [ ] 4 2b Pset two due:2026-09-04 ^d1".toList,
        "- [ ] 5 2h Lab session at:2026-09-02T10:00/12:00 ^x2".toList,
        "- [ ] 2 1b Pset three due:2026-09-05T23:59 ^d4".toList, "# Later".toList,
        "- [ ] 1 1b Someday ^a2".toList]] := by
  decide

set_option maxRecDepth 40000 in
/-- **The report names the route.**  Each overdue line is `moveOverdue` from
document 0 into the backlog (document 3), with no stamp; the demoted ones are `copy`
into the month (document 2), stamped `W36`; minutes at a 50-minute block. -/
theorem the_week_close_reports_the_overdue_route :
    closedReport week closeOverdueWitness = some
      [⟨"d1".toList, week, .moveOverdue, 0, 3, none, some (Arith.posOfNat 100)⟩,
       ⟨"d2".toList, week, .copy, 0, 2, some (.week 36), some (Arith.posOfNat 50)⟩,
       ⟨"d3".toList, week, .copy, 0, 2, some (.week 36), some (Arith.posOfNat 50)⟩,
       ⟨"x2".toList, week, .moveOverdue, 0, 3, none, some (Arith.posOfNat 120)⟩,
       ⟨"d4".toList, week, .moveOverdue, 0, 3, none, some (Arith.posOfNat 50)⟩] := by
  decide

theorem the_close_overdue_witness_loads : loadsOk closeOverdueWitness = true := by decide

/-- The loaded overdue witness.  Total by `the_close_overdue_witness_loads`: the
error branch is refuted, not defaulted. -/
def closeOverduePlan : WfPlan :=
  match h : loadPlan closeOverdueWitness with
  | .ok p => p
  | .error _ => absurd the_close_overdue_witness_loads (by simp [loadsOk, h])

/-- For one id: the action the week close at `closeNow` takes, whether the line is
past due with `persist`, and — if the close succeeds — whether its bytes, box and
tombstone survived and which kind of file it ends in. -/
def overdueHypsAt (i : Id) : Option (CloseAct × Bool × Bool × DocKind) :=
  match close week closeNow 50 closeOverduePlan with
  | .ok q =>
    match closeOverduePlan.val.store.get i, q.val.store.get i with
    | some e, some f =>
      some (closeAct week closeNow closeOverduePlan.val e.val.skel, e.val.skel.overdue closeNow,
        decide (f.val.line = e.val.line ∧ f.val.status = e.val.status ∧
          f.val.archive.map Tomb.line = e.val.archive.map Tomb.line),
        docKindAt q.val f.val.live.doc)
    | _, _ => none
  | .error _ => none

set_option maxRecDepth 40000 in
/-- **The D7 and D8 laws are not vacuous.**  On the loaded plan the week close
succeeds, `^d1` meets every hypothesis of
`close_moves_a_past_due_persist_line_to_the_backlog` and ends in the backlog with
its bytes, box and tombstone unchanged; `^d2` meets those of
`close_week_files_a_dated_line_keeping_its_date` (filed, not past due) and ends in
the month file; `^x3`, a wall that is over with `on-miss:next`, is left alone.  (The
D8 law gained, at goal B3's repair, the hypothesis that the fold does not drop the
line — `close_week_files_a_dated_line_it_does_not_drop_keeping_its_date` — which
`^d2` meets: `the_dated_witness_drops_nothing`.) -/
theorem the_dated_route_hypotheses_hold_on_a_loaded_plan :
    overdueHypsAt "d1".toList = some (.overdue, true, true, .backlog) ∧
      overdueHypsAt "d2".toList = some (.file closeW36, false, false, .month) ∧
      overdueHypsAt "x3".toList = some (.stay, false, true, .week) := by
  decide

set_option maxRecDepth 40000 in
/-- The overdue witness has no `@parent`, so the week close drops nothing: `^d2` is
filed, not dropped. -/
theorem the_dated_witness_drops_nothing :
    dropsInto week closeNow closeOverduePlan.val "d2".toList = none := by
  decide

/-- A month file whose `# Demoted` holds a record with a `due:` — what a week close
writes for a not-yet-due line since D8. -/
def datedRecordWitness : List ReqDoc :=
  [⟨"month/2026-09.md", some closeM09,
     ["# Outcomes".toList, "- [ ] 5 !1 Lean through ch.8 ^O1".toList, "# Demoted".toList,
      "- [-] 3 1b Essay draft due:2026-09-20 demoted:W36 ^d2".toList]⟩]

/-- The same month with the date on the **outcome** instead. -/
def datedOutcomeWitness : List ReqDoc :=
  [⟨"month/2026-09.md", some closeM09,
     ["# Outcomes".toList, "- [ ] 5 !1 Lean through ch.8 due:2026-09-30 ^O1".toList,
      "# Demoted".toList]⟩]

/-- The six item conjuncts of a request's loaded core that come before the file-kind
check, and that check — `firstItemFault` names the first that fails, so `(true,
false)` is the refusal `itemCheck: fileKindShape`.  Booleans, not the emitted
string: deciding a `String` through `jemit` does not fit the 8 GB probe. -/
def shapeFaultOf (docs : List ReqDoc) : Option (Bool × Bool) :=
  match buildEntities (placementsOf 0 docs) with
  | .ok items =>
    let c := loadCore docs items
    some (normalized c && parentsTotal c && parentsAcyclic c && afterTotal c && afterAcyclic c &&
      sectionsWf c, shapesWf c)
  | .error _ => none

set_option maxRecDepth 40000 in
/-- **D8, both directions, on loaded requests** (AGENTS §5.8).  A dated `# Demoted`
record loads; a dated outcome outside `# Demoted` does not, and the one item check
it fails is the file-kind check — `itemCheck: fileKindShape` on the wire.  The
narrowing exempted the records and nothing else (`a_dated_month_outcome_is_rejected`,
Plan.lean). -/
theorem a_dated_record_loads_and_a_dated_outcome_does_not :
    loadsOk datedRecordWitness = true ∧ loadsOk datedOutcomeWitness = false ∧
      shapeFaultOf datedOutcomeWitness = some (true, false) := by
  decide

/-- The loaded dated-record witness. -/
def datedRecordPlan : WfPlan :=
  match h : loadPlan datedRecordWitness with
  | .ok p => p
  | .error _ => absurd a_dated_record_loads_and_a_dated_outcome_does_not.1 (by simp [loadsOk, h])

set_option maxRecDepth 40000 in
/-- **`month_items_are_outcomes`, refuted since D8.**  Its statement, quantifier for
quantifier — every month placement has shape `none` — is false of a loaded plan: the
`# Demoted` record `^d2` sits in a month file with a `due:`.  What holds is
`month_items_outside_demoted_are_undated` (Plan.lean). -/
theorem a_dated_demoted_record_is_a_month_item_with_a_date :
    ¬ ∀ (p : WfPlan) (i : Id) (e : Entity), p.val.store.get i = some e →
      docKindAt p.val e.val.live.doc = DocKind.month → e.val.shape = Field.Shape.none := by
  intro hall
  have hw : (datedRecordPlan.val.store.get "d2".toList).map (fun e =>
      (decide (docKindAt datedRecordPlan.val e.val.live.doc = DocKind.month),
        decide (e.val.shape = Field.Shape.none))) = some (true, false) := by decide
  cases hg : datedRecordPlan.val.store.get "d2".toList with
  | none => rw [hg] at hw; cases hw
  | some e =>
    rw [hg] at hw
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq,
      decide_eq_false_iff_not] at hw
    exact hw.2 (hall _ _ e hg hw.1)

def exampleNow : Day := Cal.toDay ⟨2026, 9, 14⟩
def exampleW38 : Region := ⟨week, Cal.weekOrdinal exampleNow⟩

/-- §4.3's example week, month and backlog **byte for byte** (`tm/templates/example/`,
what `tm init --example` writes), with the backlog's `# Overdue` appended at its end
and the live week 2026-W38 as its initial text — the two things the host hands over
for a close (README gap 56's host half). -/
def exampleWeekWitness : List ReqDoc :=
  [⟨"week/2026-W37.md", some closeW37,
     ["---".toList,
      "week: 2026-W37".toList,
      "window: 2026-09-07..2026-09-13".toList,
      "budget: 25".toList,
      "planned: 20".toList,
      "---".toList,
      "# Milestones".toList,
      "- [ ] 5 6b Finish ch.5 exercises        @O1 ^m1".toList,
      "- [ ] 4 6b Rollback path passes tests   @O2 ^m2".toList,
      "- [ ] 5 3b Read ch.6                    @O1 ^m3".toList,
      "- [ ] 2 2b Pick winter courses          @O3 ^m4".toList,
      "- [ ] 4 6b CS 234 pset 2                @O3 due:2026-09-11T23:59 max:2b/d ^d1".toList,
      "- [ ] 5 2h Midterm                      @O3 at:2026-10-20T10:00/12:00 loc:JCL ^x1".toList,
      "- [ ] 5 8b Midterm review               @x1 ^x2".toList,
      "".toList,
      "# Tasks".toList,
      "- [ ] 5 1b Read ch.6 §1–2               @m3 ^t1".toList,
      "- [>] 4 2b Exercises 5.3–5.5            @m1 est:1b ^t3".toList,
      "- [ ] 3 1b Claude Code drafts tests     @m2 ^t4".toList,
      "- [ ] 3 1b Review the drafts            @m2 after:^t4 ^t5".toList]⟩,
   ⟨"week/2026-W38.md", some exampleW38,
     ["---".toList,
      "week: 2026-W38".toList,
      "window: 2026-09-14..2026-09-20".toList,
      "---".toList]⟩,
   ⟨"month/2026-09.md", some closeM09,
     ["---".toList,
      "month: 2026-09".toList,
      "---".toList,
      "# Outcomes".toList,
      "- [ ] 5 !1 Lean: through ch.8 of the tutorial          ^O1".toList,
      "- [ ] 4 !1 Soundcode: end-to-end demo runs             ^O2".toList,
      "- [ ] 2 !3 Winter course selection + admin done        ^O3".toList,
      "".toList,
      "# Demoted".toList,
      "- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2".toList]⟩,
   ⟨"backlog.md", none,
     ["# Untied".toList,
      "- [ ] 2 30m Insurance claim for the bike  ^a1".toList,
      "- [ ] 1 Pick up package  win:2026-09-07T09:00/21:00 dur:20m ^a3".toList,
      "- [?] 2 15m Ask Prof. Lee about the reading group  on-event:reply/7d waiting:2026-09-05 ^a4".toList,
      "".toList,
      "# Dated, far out".toList,
      "- [ ] 5 10b Workshop paper draft  @O2 due:2026-11-20 #soundcode ^d2".toList,
      "".toList,
      "## series:cell-bio".toList,
      "- [x] 4 4b Cell Biology vol. 1 ^c1".toList,
      "- [ ] 4 4b Cell Biology vol. 2 ^c2".toList,
      "- [ ] 4 4b Cell Biology vol. 3 ^c3".toList,
      "# Overdue".toList]⟩]

set_option maxRecDepth 100000 in
/-- **§4.3's example week closes a week after init** (README gap 55, closed).  At
Monday 2026-09-14: every open milestone of 2026-W37 is left behind as `[-]`; `^d1`
(`due:2026-09-11T23:59`, past due, `persist`) is not among them — it sits at the end
of the backlog's `# Overdue`, `[ ]`, its `due:` and every byte kept; `^m2` is **one**
merged record in `# Demoted` (README gap 53); the midterm wall is carried into
2026-W38; no refusal.  Since goal B3's repair the four tasks under `^m1`, `^m2` and
`^m3` — milestones this close files from the same file — are **dropped**, `[~]` in
place, and no record of them is filed; each milestone's own estimate covers them
(`^m1` `6b` over `^t3`'s `est:1b`, `^m2` `6b` over `1b + 1b`, `^m3` `3b` over `1b`), so
§6.4's `max` writes nothing on the three records.  `^x2` is not dropped: its parent,
the wall `^x1`, is carried, not filed. -/
theorem the_example_week_closes_with_d1_in_the_backlog_overdue :
    (loadedPlan? exampleWeekWitness).bind (fun p => closeResultLines (close week exampleNow 50 p)) = some
      [["---".toList,
        "week: 2026-W37".toList,
        "window: 2026-09-07..2026-09-13".toList,
        "budget: 25".toList,
        "planned: 20".toList,
        "---".toList,
        "# Milestones".toList,
        "- [-] 5 6b Finish ch.5 exercises        @O1 ^m1".toList,
        "- [-] 4 6b Rollback path passes tests   @O2 ^m2".toList,
        "- [-] 5 3b Read ch.6                    @O1 ^m3".toList,
        "- [-] 2 2b Pick winter courses          @O3 ^m4".toList,
        "- [-] 5 8b Midterm review               @x1 ^x2".toList,
        "".toList,
        "# Tasks".toList,
        "- [~] 5 1b Read ch.6 §1–2               @m3 ^t1".toList,
        "- [~] 4 2b Exercises 5.3–5.5            @m1 est:1b ^t3".toList,
        "- [~] 3 1b Claude Code drafts tests     @m2 ^t4".toList,
        "- [~] 3 1b Review the drafts            @m2 after:^t4 ^t5".toList],
       ["---".toList,
        "week: 2026-W38".toList,
        "window: 2026-09-14..2026-09-20".toList,
        "---".toList,
        "- [ ] 5 2h Midterm                      @O3 at:2026-10-20T10:00/12:00 loc:JCL ^x1".toList],
       ["---".toList,
        "month: 2026-09".toList,
        "---".toList,
        "# Outcomes".toList,
        "- [ ] 5 !1 Lean: through ch.8 of the tutorial          ^O1".toList,
        "- [ ] 4 !1 Soundcode: end-to-end demo runs             ^O2".toList,
        "- [ ] 2 !3 Winter course selection + admin done        ^O3".toList,
        "".toList,
        "# Demoted".toList,
        "- [-] 5 6b Finish ch.5 exercises        @O1 demoted:W37 ^m1".toList,
        "- [-] 4 6b Rollback path passes tests   @O2 demoted:W37 ^m2".toList,
        "- [-] 5 3b Read ch.6                    @O1 demoted:W37 ^m3".toList,
        "- [-] 2 2b Pick winter courses          @O3 demoted:W37 ^m4".toList,
        "- [-] 5 8b Midterm review               @x1 demoted:W37 ^x2".toList],
       ["# Untied".toList,
        "- [ ] 2 30m Insurance claim for the bike  ^a1".toList,
        "- [ ] 1 Pick up package  win:2026-09-07T09:00/21:00 dur:20m ^a3".toList,
        "- [?] 2 15m Ask Prof. Lee about the reading group  on-event:reply/7d waiting:2026-09-05 ^a4".toList,
        "".toList,
        "# Dated, far out".toList,
        "- [ ] 5 10b Workshop paper draft  @O2 due:2026-11-20 #soundcode ^d2".toList,
        "".toList,
        "## series:cell-bio".toList,
        "- [x] 4 4b Cell Biology vol. 1 ^c1".toList,
        "- [ ] 4 4b Cell Biology vol. 2 ^c2".toList,
        "- [ ] 4 4b Cell Biology vol. 3 ^c3".toList,
        "# Overdue".toList,
        "- [ ] 4 6b CS 234 pset 2                @O3 due:2026-09-11T23:59 max:2b/d ^d1".toList]] := by
  decide

/-! ## Stage 4 final, step 3: a parent is read off its line (the owner's D6)

`Core.parent` was the one §3.1 field stored beside the line, and it was `none` on
every record the boundary built — so `parentsTotal` and `parentsAcyclic` sat in
`planWf` unable to fire, and §3.2's `effectiveShape` prep rule, `effectiveCi`
inheritance and `rootPrio` were proved about a hierarchy no loaded plan had
(README gap 22, AGENTS §5.2).  Since D6 it is `Field.parentRef` of the line
(State.lean), and both checks are whole-tree refusals by name.

Everything below is decided on requests the loader really reads.  The refusals are
stated on the wire's own value (`loadPlan … = .error …itemCheck…`), but what is
**decided** is booleans — the conjuncts `loadPlan` tests, in its order — and the
name is read off them by `loadPlan_itemCheck`, not by evaluating a `String` (the
8 GB probe that deciding an emitted string does not fit, README "Stage 4 final",
step 2). -/

/-- **`loadPlan`'s item refusal, as a lemma.**  When the entities build and the
three plan conjuncts before `itemsWf` hold, a failing `itemsWf` is refused with
`itemCheck` and `firstItemFault`'s name — nothing else. -/
theorem loadPlan_itemCheck (docs : List ReqDoc) (items : List (Id × Entity))
    (hb : buildEntities (placementsOf 0 docs) = .ok items)
    (h1 : pathsDistinct (loadCore docs items) = true)
    (h2 : sitesInRange (loadCore docs items) = true)
    (h3 : demotionsOriented (loadCore docs items) = true)
    (h4 : itemsWf (loadCore docs items) = false) :
    loadPlan docs = .error (jone "err"
      (jone "itemCheck" (.str (firstItemFault (loadCore docs items)).toList))) := by
  unfold loadPlan
  split
  · rename_i e he; rw [hb] at he; cases he
  · rename_i its hits
    rw [hb] at hits
    cases hits
    rw [dif_pos h1, dif_pos h2, dif_pos h3, dif_neg (by rw [h4]; simp)]

/-- The whole-tree facts `loadPlan` tests before `itemsWf`, then the first three of
`itemsWf`'s seven: `pathsDistinct`, `sitesInRange`, `demotionsOriented`,
`normalized`, `parentsTotal`, `parentsAcyclic`. -/
def parentFactsOf (docs : List ReqDoc) : Option (List Bool) :=
  match buildEntities (placementsOf 0 docs) with
  | .ok items =>
    let c := loadCore docs items
    some [pathsDistinct c, sitesInRange c, demotionsOriented c, normalized c, parentsTotal c,
      parentsAcyclic c]
  | .error _ => none

/-- **A dangling parent refuses the whole tree, by name.**  Read off the facts:
the plan conjuncts and the rank check pass and `parentsTotal` fails, so
`firstItemFault` is `danglingParent` whatever follows it. -/
theorem loadPlan_refuses_a_dangling_parent (docs : List ReqDoc) (b : Bool)
    (h : parentFactsOf docs = some [true, true, true, true, false, b]) :
    loadPlan docs = .error (jone "err" (jone "itemCheck" (.str "danglingParent".toList))) := by
  unfold parentFactsOf at h
  split at h
  · rename_i items hb
    simp only [Option.some.injEq, List.cons.injEq, and_true] at h
    obtain ⟨h1, h2, h3, h4, h5, _⟩ := h
    rw [loadPlan_itemCheck docs items hb h1 h2 h3 (by simp [itemsWf, h5])]
    simp [firstItemFault, h4, h5]
  · simp at h

/-- **A parent cycle refuses the whole tree, by name** — `parentCycle`, not
`danglingParent`: every link resolves and the walk does not end. -/
theorem loadPlan_refuses_a_parent_cycle (docs : List ReqDoc)
    (h : parentFactsOf docs = some [true, true, true, true, true, false]) :
    loadPlan docs = .error (jone "err" (jone "itemCheck" (.str "parentCycle".toList))) := by
  unfold parentFactsOf at h
  split at h
  · rename_i items hb
    simp only [Option.some.injEq, List.cons.injEq, and_true] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    rw [loadPlan_itemCheck docs items hb h1 h2 h3 (by simp [itemsWf, h6])]
    simp [firstItemFault, h4, h5, h6]
  · simp at h

/-- §4.3's hierarchy, in five lines: two September outcomes with explicit
priorities; a milestone `^m1` under `^O1` that writes **no** `ci` digit; the midterm
wall `^x1` under `^O3` and its shapeless prep child `^x2`; and `^t1`, a task under
`^m1`, with no `ci` and no `!k` of its own.  Every link resolves inside the request
— a week line's `@O1` against the month file it came with, which is why the host
hands the kernel whole trees. -/
def parentTreeWitness : List ReqDoc :=
  [⟨"week/2026-W37.md", some closeW37,
     ["# Milestones".toList,
      "- [ ] 6b Finish ch.5 exercises        @O1 ^m1".toList,
      "- [ ] 5 2h Midterm                      @O3 at:2026-10-20T10:00/12:00 loc:JCL ^x1".toList,
      "- [ ] 5 8b Midterm review               @x1 ^x2".toList,
      "# Tasks".toList,
      "- [ ] 1b Read ch.6 §1–2               @m1 ^t1".toList]⟩,
   ⟨"month/2026-09.md", some closeM09,
     ["# Outcomes".toList,
      "- [ ] 5 !1 Lean: through ch.8 of the tutorial          ^O1".toList,
      "- [ ] 2 !3 Winter course selection + admin done        ^O3".toList]⟩]

/-- The same tree with one typo: `^m1` names `@O9`, which no line carries. -/
def parentTypoWitness : List ReqDoc :=
  [⟨"week/2026-W37.md", some closeW37,
     ["# Milestones".toList,
      "- [ ] 6b Finish ch.5 exercises        @O9 ^m1".toList,
      "- [ ] 5 2h Midterm                      @O3 at:2026-10-20T10:00/12:00 loc:JCL ^x1".toList,
      "- [ ] 5 8b Midterm review               @x1 ^x2".toList,
      "# Tasks".toList,
      "- [ ] 1b Read ch.6 §1–2               @m1 ^t1".toList]⟩,
   ⟨"month/2026-09.md", some closeM09,
     ["# Outcomes".toList,
      "- [ ] 5 !1 Lean: through ch.8 of the tutorial          ^O1".toList,
      "- [ ] 2 !3 Winter course selection + admin done        ^O3".toList]⟩]

/-- The same tree with `plan-conflicts`' ouroboros added: `^y1` under `^y2` and
`^y2` under `^y1`.  Both links resolve. -/
def parentCycleWitness : List ReqDoc :=
  [⟨"week/2026-W37.md", some closeW37,
     ["# Milestones".toList,
      "- [ ] 6b Finish ch.5 exercises        @O1 ^m1".toList,
      "- [ ] 5 2h Midterm                      @O3 at:2026-10-20T10:00/12:00 loc:JCL ^x1".toList,
      "- [ ] 5 8b Midterm review               @x1 ^x2".toList,
      "# Tasks".toList,
      "- [ ] 1b Read ch.6 §1–2               @m1 ^t1".toList,
      "- [ ] 3 1b Ouroboros head               @y2 ^y1".toList,
      "- [ ] 3 1b Ouroboros tail               @y1 ^y2".toList]⟩,
   ⟨"month/2026-09.md", some closeM09,
     ["# Outcomes".toList,
      "- [ ] 5 !1 Lean: through ch.8 of the tutorial          ^O1".toList,
      "- [ ] 2 !3 Winter course selection + admin done        ^O3".toList]⟩]

set_option maxRecDepth 40000 in
/-- **A tree whose links all resolve loads.** -/
theorem the_parent_tree_loads : loadsOk parentTreeWitness = true := by decide

set_option maxRecDepth 40000 in
/-- **§4.3's literal example tree loads with its parents read** — every `@O1`,
`@m2`, `@x1` of `tm init --example`'s week, month and backlog resolves inside the
request (the witness `the_example_week_closes_with_d1_in_the_backlog_overdue`
closes; this is the load alone, decided). -/
theorem the_example_tree_loads_with_its_parents : loadsOk exampleWeekWitness = true := by decide

set_option maxRecDepth 40000 in
/-- The typo'd tree's facts: every conjunct before `parentsTotal` holds, and
`parentsTotal` does not. -/
theorem the_typo_tree_fails_parentsTotal_only :
    parentFactsOf parentTypoWitness = some [true, true, true, true, false, true] := by decide

set_option maxRecDepth 40000 in
/-- The cycle tree's facts: every link resolves, and `parentsAcyclic` fails. -/
theorem the_cycle_tree_fails_parentsAcyclic_only :
    parentFactsOf parentCycleWitness = some [true, true, true, true, true, false] := by decide

/-- **D6, one direction: a typo'd `@O9` refuses the whole tree, by name** —
`{"err":{"itemCheck":"danglingParent"}}`, and no plan is built, so no command runs
and nothing is written. -/
theorem a_typod_parent_refuses_the_whole_tree_by_name :
    loadPlan parentTypoWitness =
      .error (jone "err" (jone "itemCheck" (.str "danglingParent".toList))) :=
  loadPlan_refuses_a_dangling_parent _ true the_typo_tree_fails_parentsTotal_only

/-- **D6, the other refusal: a two-line parent cycle refuses the whole tree, by
name** — `{"err":{"itemCheck":"parentCycle"}}`. -/
theorem a_parent_cycle_refuses_the_whole_tree_by_name :
    loadPlan parentCycleWitness =
      .error (jone "err" (jone "itemCheck" (.str "parentCycle".toList))) :=
  loadPlan_refuses_a_parent_cycle _ the_cycle_tree_fails_parentsAcyclic_only

/-- The loaded parent tree.  Total by `the_parent_tree_loads`: the error branch is
refuted, not defaulted. -/
def parentTreePlan : WfPlan :=
  match h : loadPlan parentTreeWitness with
  | .ok p => p
  | .error _ => absurd the_parent_tree_loads (by simp [loadsOk, h])

/-- What `effectiveShape_prep` assumes of an id, read off a plan: its own shape,
its parent, and the parent's shape. -/
def prepHypsAt (p : PlanCore) (i : Id) : Option (Field.Shape × Option Id × Option Field.Shape) :=
  (p.store.get i).map (fun e => (e.val.shape, e.val.parent, e.val.parent.map (shapeOf p)))

set_option maxRecDepth 40000 in
/-- **§3.2's prep rule fires on a loaded plan.**  `^x2` writes no date and its
parent `^x1` is the midterm interval, so `effectiveShape_prep`'s hypotheses hold and
its effective shape is a point due at the exam's start, 2026-10-20 10:00.  Before
D6 its parent was `none` and the same call answered `Shape.none`. -/
theorem the_prep_rule_fires_on_a_loaded_plan :
    prepHypsAt parentTreePlan.val "x2".toList =
        some (Field.Shape.none, some "x1".toList,
          some (Field.Shape.interval ⟨Cal.toDay ⟨2026, 10, 20⟩, ⟨10 * 60, by decide⟩⟩
                               ⟨Cal.toDay ⟨2026, 10, 20⟩, ⟨12 * 60, by decide⟩⟩)) ∧
      effectiveShape parentTreePlan.val "x2".toList =
        Field.Shape.point (Field.Moment.dateTime (Cal.toDay ⟨2026, 10, 20⟩) ⟨10 * 60, by decide⟩) := by
  decide

set_option maxRecDepth 40000 in
/-- **§3.1's `ci` default fires on a loaded plan: "the parent's, else 3".**  `^t1`
and its parent `^m1` write no `ci`, and `^O1` writes `5`, so `^t1`'s effective ci is
`5` through two inherited links (`effectiveCi_inherits`, twice).  Before D6 the walk
stopped at `^t1` and answered the default `3`. -/
theorem effectiveCi_inherits_on_a_loaded_plan :
    (parentTreePlan.val.store.get "t1".toList).map (fun e => (e.val.ci, e.val.parent)) =
        some (none, some "m1".toList) ∧
      (parentTreePlan.val.store.get "m1".toList).map (fun e => (e.val.ci, e.val.parent)) =
        some (none, some "O1".toList) ∧
      effectiveCi parentTreePlan.val "t1".toList = 5 := by
  decide

set_option maxRecDepth 40000 in
/-- **§3.2's `root_priority` fires on a loaded plan — §7.1's `k = root_priority`.**
`^t1` and `^m1` carry no `!k`; the walk climbs to `^O1` and reads `!1` there (held
zero-based, `0`), and `^x2` climbs through `^x1` to `^O3`'s `!3` (`2`).  Before D6
every record was its own root and `rootPrio` read `^t1`'s own `none`. -/
theorem rootPrio_reads_the_root_on_a_loaded_plan :
    (parentTreePlan.val.store.get "t1".toList).map (fun e => e.val.prio) = some none ∧
      rootPrio parentTreePlan.val "t1".toList = some ⟨0, by decide⟩ ∧
      rootPrio parentTreePlan.val "x2".toList = some ⟨2, by decide⟩ := by
  decide


/-! ## Stage 4 final, step 4: goal B3's child fold, on a loaded plan

§6.3's week row: "Unfinished children are dropped from the week file (their remaining
is folded into the parent's `est:`)."  `Close.lean` performs it (`dropsInto`,
`foldedMinutes`, `foldEst`) and proves its law, §6.4's `max`
(`close_week_folds_dropped_children_by_max`).  Everything below is decided on one
request the loader reads — `closeFoldWitness`: a stale `2b` milestone with `2b + 1b`
of subtasks and a grandchild with no estimate, a `6b` milestone with two `1b`
subtasks, one of them dated and with a standing `# Demoted` record — closed at Monday
2026-09-07, and every refutation reads its facts off that one close (each decision
probed alone under an 8 GB cap first; README "Stage 4 final, step 4"). -/

/-- 2026-W36 with two milestones and their subtasks, and September's `# Demoted`
holding a standing record of the dated subtask `^c5`. -/
def closeFoldWitness : List ReqDoc :=
  [⟨"week/2026-W36.md", some closeW36,
     ["# Milestones".toList,
      "- [ ] 2b Stale milestone ^p1".toList,
      "- [ ] 6b Covered milestone ^p2".toList,
      "# Tasks".toList,
      "- [ ] 2b Part one @p1 ^c1".toList,
      "- [ ] 1b Part two @p1 ^c2".toList,
      "- [ ] Grandchild @c1 ^c4".toList,
      "- [ ] 1b Covered part @p2 ^c3".toList,
      "- [ ] 1b Dated part @p2 due:2026-09-30 ^c5".toList]⟩,
   ⟨"month/2026-09.md", some closeM09,
     ["# Outcomes".toList, "# Demoted".toList,
      "- [-] 1b Dated part @p2 est:1b due:2026-09-30 demoted:W35 ^c5".toList]⟩]

set_option maxRecDepth 40000 in
/-- The fold witness loads. -/
theorem the_close_fold_witness_loads : loadsOk closeFoldWitness = true := by decide

/-- The loaded fold witness.  Total by `the_close_fold_witness_loads`: the error branch
is refuted, not defaulted. -/
def closeFoldPlan : WfPlan :=
  match h : loadPlan closeFoldWitness with
  | .ok p => p
  | .error _ => absurd the_close_fold_witness_loads (by simp [loadsOk, h])

set_option maxRecDepth 40000 in
/-- **§6.3's week row folds dropped children into their parents, on a loaded plan.**
At Monday 2026-09-07, 2026-W36 closes: its two milestones are left behind as `[-]`
and their records filed into September's `# Demoted`; every task under them is
dropped, `[~]` in place, and filed nowhere.  `^p1` (`2b`) had `2b + 1b` of subtasks
dropped with it — and `^c4`, a grandchild with no estimate of its own, counted at `0`
— so its record carries §6.4's `max`, `est:3b`; `^p2` (`6b`) covers its `1b + 1b`, so
its record is the line with only the stamp set.  `^c5`'s standing record stays where
it was, unmerged. -/
theorem the_week_close_folds_dropped_children_on_a_loaded_plan :
    closedFileLines week closeFoldWitness = some
      [["# Milestones".toList,
        "- [-] 2b Stale milestone ^p1".toList,
        "- [-] 6b Covered milestone ^p2".toList,
        "# Tasks".toList,
        "- [~] 2b Part one @p1 ^c1".toList,
        "- [~] 1b Part two @p1 ^c2".toList,
        "- [~] Grandchild @c1 ^c4".toList,
        "- [~] 1b Covered part @p2 ^c3".toList,
        "- [~] 1b Dated part @p2 due:2026-09-30 ^c5".toList],
       ["# Outcomes".toList, "# Demoted".toList,
        "- [-] 1b Dated part @p2 est:1b due:2026-09-30 demoted:W35 ^c5".toList,
        "- [-] 2b Stale milestone est:3b demoted:W36 ^p1".toList,
        "- [-] 6b Covered milestone demoted:W36 ^p2".toList]] := by
  decide

set_option maxRecDepth 40000 in
/-- **What the fold computes on the loaded witness**: each task's line its minutes go
to — the grandchild `^c4` past its dropped parent `^c1` to `^p1` — and each milestone's
folded minutes at a 50-minute block: `^p1` `100 + 50 + 0`, `^p2` `50 + 50`. -/
theorem the_fold_on_the_loaded_witness :
    (["p1", "p2", "c1", "c2", "c4", "c3", "c5"].map (fun i =>
      (dropsInto week closeNow closeFoldPlan.val i.toList,
        foldedMinutes week closeNow 50 closeFoldPlan.val i.toList))) =
      [(none, 150), (none, 100), (some "p1".toList, 0), (some "p1".toList, 0), (some "p1".toList, 0),
        (some "p2".toList, 0), (some "p2".toList, 0)] := by
  decide

set_option maxRecDepth 40000 in
/-- **The report names the fold**: two `copyFolding` records and five `dropIntoParent`
lines, each dropped line staying in document 0 with no stamp. -/
theorem the_week_close_reports_the_fold :
    closedReport week closeFoldWitness = some
      [⟨"p1".toList, week, .copyFolding, 0, 1, some (.week 36), some (Arith.posOfNat 150)⟩,
       ⟨"p2".toList, week, .copyFolding, 0, 1, some (.week 36), some (Arith.posOfNat 300)⟩,
       ⟨"c1".toList, week, .dropIntoParent, 0, 0, none, some (Arith.posOfNat 100)⟩,
       ⟨"c2".toList, week, .dropIntoParent, 0, 0, none, some (Arith.posOfNat 50)⟩,
       ⟨"c4".toList, week, .dropIntoParent, 0, 0, none, none⟩,
       ⟨"c3".toList, week, .dropIntoParent, 0, 0, none, some (Arith.posOfNat 50)⟩,
       ⟨"c5".toList, week, .dropIntoParent, 0, 0, none, some (Arith.posOfNat 50)⟩] := by
  decide

/-- The fold witness after `close week closeNow 50`, observed. -/
def foldClosed {α : Type} (obs : WfPlan → α) : Option α :=
  match close week closeNow 50 closeFoldPlan with
  | .ok q    => some (obs q)
  | .error _ => none

/-- One id's entity before and after the fold witness's week close, observed together. -/
def beforeAfterFoldClose {α : Type} (i : Id) (obs : WfPlan → Entity → Entity → α) (q : WfPlan) :
    Option α :=
  match closeFoldPlan.val.store.get i, q.val.store.get i with
  | some e, some f => some (obs q e f)
  | _, _ => none

/-- The facts every fold law reads off one line, as numbers (a `Bool` as `0`/`1`):
whether the close files it, whether it is not dropped, what it folds, its readings
before, carried and after at a 50-minute block, whether it has a record, whether it is
`[~]` afterwards, and whether it ends in the file `closeTo` names. -/
def foldFacts (q : WfPlan) (i : Id) (e f : Entity) : List Nat :=
  [(filesLine week closeNow closeFoldPlan.val e.val.skel).toNat,
   (dropsInto week closeNow closeFoldPlan.val i).isNone.toNat,
   foldedMinutes week closeNow 50 closeFoldPlan.val i,
   remainingOf 50 e.val.line, remainingOf 50 (carriedLine e), remainingOf 50 f.val.line,
   e.val.archive.isSome.toNat,
   (decide (f.val.status = .settled .dropped)).toNat,
   (decide (docRegion q.val f.val.live.doc = some (closeTo week closeNow))).toNat]

set_option maxRecDepth 40000 in
/-- **The laws' hypotheses, and what they give, on the loaded witness.**  `^p1`: filed,
not dropped, folding 150 minutes over a carried 100, reading 150 after, no record, in
September.  `^p2`: filed, not dropped, folding 100 under its own 300, reading 300.
`^c3`: filed and dropped, 50 minutes, `[~]`, still in 2026-W36.  `^c5`: the same, and
it has a standing record. -/
theorem the_fold_facts_on_the_loaded_witness :
    foldClosed (α := List (Option (List Nat))) (fun q => ["p1", "p2", "c3", "c5"].map (fun i =>
      beforeAfterFoldClose i.toList (fun q e f => foldFacts q i.toList e f) q)) =
      some [some [1, 1, 150, 100, 100, 150, 0, 0, 1],
            some [1, 1, 100, 300, 300, 300, 0, 0, 1],
            some [1, 0, 0, 50, 50, 50, 0, 1, 0],
            some [1, 0, 0, 50, 50, 50, 1, 1, 0]] := by
  decide

set_option maxRecDepth 40000 in
/-- The rest of what the refutations read off the loaded witness: `^c3`'s parent is
`^p2`; `^c5` is not recurring and is due on or after Monday; the report names `^c3`
`dropIntoParent` in document 0; `^p1` and `^c1` are taken by one action from one file,
`^p1` above, and end in different files. -/
theorem the_fold_witness_links_and_dates :
    parentStep closeFoldPlan.val "c3".toList = some "p2".toList ∧
      (closeFoldPlan.val.store.get "c5".toList).map (fun e =>
        (decide (e.val.recur = Field.Recur.none),
         match e.val.shape with
         | .point m => decide (closeNow ≤ m.day)
         | _        => false)) = some (true, true) ∧
      ((closeReport week closeNow blockMin50 closeFoldPlan.val).find? (fun x => x.id == "c3".toList)).map
        (fun x => (x.did, x.dst)) = some (.dropIntoParent, 0) ∧
      (match closeFoldPlan.val.store.get "p1".toList, closeFoldPlan.val.store.get "c1".toList with
       | some a, some b =>
         decide (closeAct week closeNow closeFoldPlan.val b.val.skel = closeAct week closeNow closeFoldPlan.val a.val.skel) &&
           decide (a.val.live.doc = b.val.live.doc) && decide (a.val.live.rank < b.val.live.rank)
       | _, _ => false) = true ∧
      foldClosed (fun q => decide ((q.val.store.get "p1".toList).map (fun f => f.val.live.doc) ≠
        (q.val.store.get "c1".toList).map (fun f => f.val.live.doc))) = some true := by
  decide

theorem toNat_eq_one {b : Bool} (h : b.toNat = 1) : b = true := by cases b <;> simp_all
theorem toNat_eq_zero {b : Bool} (h : b.toNat = 0) : b = false := by cases b <;> simp_all

theorem beforeAfterFoldClose_some {i : Id} {q : WfPlan} {l : List Nat}
    (h : beforeAfterFoldClose i (fun q e f => foldFacts q i e f) q = some l) :
    ∃ e f, closeFoldPlan.val.store.get i = some e ∧ q.val.store.get i = some f ∧ foldFacts q i e f = l := by
  unfold beforeAfterFoldClose at h
  split at h
  · rename_i e f he hf
    injection h with h
    exact ⟨e, f, he, hf, h⟩
  · simp at h

/-- The four lines' facts under the fold witness's week close, unpacked. -/
theorem fold_facts {q : WfPlan} (h : close week closeNow 50 closeFoldPlan = .ok q) :
    (∃ e f, closeFoldPlan.val.store.get "p1".toList = some e ∧ q.val.store.get "p1".toList = some f ∧
      foldFacts q "p1".toList e f = [1, 1, 150, 100, 100, 150, 0, 0, 1]) ∧
    (∃ e f, closeFoldPlan.val.store.get "p2".toList = some e ∧ q.val.store.get "p2".toList = some f ∧
      foldFacts q "p2".toList e f = [1, 1, 100, 300, 300, 300, 0, 0, 1]) ∧
    (∃ e f, closeFoldPlan.val.store.get "c3".toList = some e ∧ q.val.store.get "c3".toList = some f ∧
      foldFacts q "c3".toList e f = [1, 0, 0, 50, 50, 50, 0, 1, 0]) ∧
    (∃ e f, closeFoldPlan.val.store.get "c5".toList = some e ∧ q.val.store.get "c5".toList = some f ∧
      foldFacts q "c5".toList e f = [1, 0, 0, 50, 50, 50, 1, 1, 0]) := by
  have hw := the_fold_facts_on_the_loaded_witness
  unfold foldClosed at hw
  rw [h] at hw
  simp only [List.map_cons, List.map_nil, Option.some.injEq, List.cons.injEq] at hw
  obtain ⟨h1, h2, h3, h4, -⟩ := hw
  exact ⟨beforeAfterFoldClose_some h1, beforeAfterFoldClose_some h2, beforeAfterFoldClose_some h3,
    beforeAfterFoldClose_some h4⟩

theorem foldFacts_eq {q : WfPlan} {i : Id} {e f : Entity} {a b c d e' f' g h k : Nat}
    (hf : foldFacts q i e f = [a, b, c, d, e', f', g, h, k]) :
    (filesLine week closeNow closeFoldPlan.val e.val.skel).toNat = a ∧
      (dropsInto week closeNow closeFoldPlan.val i).isNone.toNat = b ∧
      foldedMinutes week closeNow 50 closeFoldPlan.val i = c ∧
      remainingOf 50 e.val.line = d ∧ remainingOf 50 (carriedLine e) = e' ∧
      remainingOf 50 f.val.line = f' ∧ e.val.archive.isSome.toNat = g ∧
      (decide (f.val.status = .settled .dropped)).toNat = h ∧
      (decide (docRegion q.val f.val.live.doc = some (closeTo week closeNow))).toNat = k := by
  unfold foldFacts at hf
  simp only [List.cons.injEq] at hf
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.1,
    hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.1⟩

theorem archive_none_of_toNat {e : Entity} (h : e.val.archive.isSome.toNat = 0) : e.val.archive = none := by
  have := toNat_eq_zero h
  cases ha : e.val.archive with
  | none => rfl
  | some _ => rw [ha] at this; cases this

/-- **Goal B3 (P\*), refuted — discharged from `Goals.lean` by refute-and-rename.**
The negation of `close_week_folds_a_dropped_child_into_its_parent`, quantifier for
quantifier (its `close week now p` is `close week now bm p` since the close reads the
block length, at the `bm` the goal already bound).  The goal added a dropped child's
remaining to its parent's, and §6.4 makes a parent's own estimate cover its
decomposition: `^p2` (`6b`, 300 minutes) with its `1b` subtask `^c3` (50) dropped
carries 300, not 350.  What holds is `close_week_folds_dropped_children_by_max` and,
for the child, `close_week_keeps_a_dropped_childs_remaining_in_its_parents_record`
(Close.lean). -/
theorem close_week_does_not_add_a_dropped_child_to_its_parent :
    ¬ ∀ (now : Day) (bm : Nat) (p q : WfPlan), close week now bm p = .ok q →
      ∀ (i j : Id) (ec ep fp fc : Entity),
        parentStep p.val j = some i →
        p.val.store.get j = some ec → p.val.store.get i = some ep →
        q.val.store.get i = some fp → q.val.store.get j = some fc →
        fc.val.status = .settled .dropped →
        remainingOf bm ep.val.line + remainingOf bm ec.val.line ≤ remainingOf bm fp.val.line := by
  intro hall
  cases h : close week closeNow 50 closeFoldPlan with
  | error x =>
    have hw := the_fold_facts_on_the_loaded_witness
    unfold foldClosed at hw; rw [h] at hw; cases hw
  | ok q =>
    obtain ⟨-, ⟨ep, fp, hep, hfp, hp2⟩, ⟨ec, fc, hec, hfc, hc3⟩, -⟩ := fold_facts h
    obtain ⟨-, -, -, hre, -, hrf, -, -, -⟩ := foldFacts_eq hp2
    obtain ⟨-, -, -, hrc, -, -, -, hdr, -⟩ := foldFacts_eq hc3
    have hdrop : fc.val.status = .settled .dropped := by simpa using toNat_eq_one hdr
    have := hall closeNow 50 closeFoldPlan q h "p2".toList "c3".toList ec ep fp fc
      the_fold_witness_links_and_dates.1 hec hep hfp hfc hdrop
    omega

/-- **`close_rewrites_a_line_only_by_stamping_or_merging_it`, refuted since B3's
repair.**  Its statement, quantifier for quantifier (at the close's new block length):
`^p1`'s record carries `est:3b`, which neither a `demoted:` write nor a merge adds — it
has no standing record.  What holds is
`close_rewrites_a_line_only_by_stamping_merging_or_folding_it` (Close.lean). -/
theorem a_folded_record_is_rewritten_beyond_its_stamp :
    ¬ ∀ (g : Grain) (now : Day) (bm : Nat) (p q : WfPlan), close g now bm p = .ok q →
      ∀ (i : Id) (e f : Entity), p.val.store.get i = some e → q.val.store.get i = some f →
        f.val.line = e.val.line ∨ (∃ ss, f.val.line = Field.setDemoted ss e.val.line) ∨
          ∃ ss t, e.val.archive = some t ∧ f.val.line = Field.setDemoted ss (carryEst t.line e.val.line) := by
  intro hall
  cases h : close week closeNow 50 closeFoldPlan with
  | error x =>
    have hw := the_fold_facts_on_the_loaded_witness
    unfold foldClosed at hw; rw [h] at hw; cases hw
  | ok q =>
    obtain ⟨⟨e, f, he, hf, hp1⟩, -⟩ := fold_facts h
    obtain ⟨-, -, -, hre, -, hrf, ha, -, -⟩ := foldFacts_eq hp1
    rcases hall week closeNow 50 closeFoldPlan q h _ e f he hf with hl | ⟨ss, hl⟩ | ⟨ss, t, hat, _⟩
    · rw [hl] at hrf; omega
    · rw [hl, Field.remainingOf_setDemoted] at hrf; omega
    · rw [archive_none_of_toNat ha] at hat; cases hat

/-- **`close_rewrites_a_line_with_no_record_only_by_stamping_it`, refuted since B3's
repair**, at `^p1`, which has no record.  What holds is
`close_rewrites_a_line_with_no_record_only_by_stamping_or_folding_it`, and, with
nothing folded, `close_rewrites_a_line_with_no_record_and_nothing_folded_only_by_stamping_it`. -/
theorem a_folded_line_with_no_record_is_rewritten_beyond_its_stamp :
    ¬ ∀ (g : Grain) (now : Day) (bm : Nat) (p q : WfPlan), close g now bm p = .ok q →
      ∀ (i : Id) (e f : Entity), p.val.store.get i = some e → q.val.store.get i = some f →
        e.val.archive = none →
        f.val.line = e.val.line ∨ ∃ ss, f.val.line = Field.setDemoted ss e.val.line := by
  intro hall
  cases h : close week closeNow 50 closeFoldPlan with
  | error x =>
    have hw := the_fold_facts_on_the_loaded_witness
    unfold foldClosed at hw; rw [h] at hw; cases hw
  | ok q =>
    obtain ⟨⟨e, f, he, hf, hp1⟩, -⟩ := fold_facts h
    obtain ⟨-, -, -, hre, -, hrf, ha, -, -⟩ := foldFacts_eq hp1
    rcases hall week closeNow 50 closeFoldPlan q h _ e f he hf (archive_none_of_toNat ha) with hl | ⟨ss, hl⟩
    · rw [hl] at hrf; omega
    · rw [hl, Field.remainingOf_setDemoted] at hrf; omega

/-- **`close_reads_every_remaining_estimate_through_demoteEst`, refuted since B3's
repair.**  `^p1`'s remaining goes from 100 to 150 minutes at a 50-minute block, and it
has no standing record whose `demoteEst` reading could explain it.  What holds is
`close_reads_every_remaining_estimate_through_demoteEst_and_the_fold` (Close.lean). -/
theorem a_folded_record_changes_a_remaining_estimate :
    ¬ ∀ (g : Grain) (now : Day) (bm : Nat) (p q : WfPlan), close g now bm p = .ok q →
      ∀ (i : Id) (e f : Entity), p.val.store.get i = some e → q.val.store.get i = some f →
        ∀ bm', remainingOf bm' f.val.line = remainingOf bm' e.val.line ∨
          ∃ t, e.val.archive = some t ∧ remainingOf bm' f.val.line =
            remainingOf bm' (demoteEst bm' (ownsEstimate e.val.line) (recordedEst bm' t.line) e).val.line := by
  intro hall
  cases h : close week closeNow 50 closeFoldPlan with
  | error x =>
    have hw := the_fold_facts_on_the_loaded_witness
    unfold foldClosed at hw; rw [h] at hw; cases hw
  | ok q =>
    obtain ⟨⟨e, f, he, hf, hp1⟩, -⟩ := fold_facts h
    obtain ⟨-, -, -, hre, -, hrf, ha, -, -⟩ := foldFacts_eq hp1
    rcases hall week closeNow 50 closeFoldPlan q h _ e f he hf 50 with hl | ⟨t, hat, _⟩
    · omega
    · rw [archive_none_of_toNat ha] at hat; cases hat

/-- **`close_keeps_the_remaining_estimate_of_a_line_with_no_record`, refuted since B3's
repair**, at `^p1`.  What holds is
`close_keeps_the_remaining_estimate_of_a_line_with_no_record_and_nothing_folded`. -/
theorem a_folded_line_with_no_record_changes_its_remaining_estimate :
    ¬ ∀ (g : Grain) (now : Day) (bm : Nat) (p q : WfPlan), close g now bm p = .ok q →
      ∀ (i : Id) (e f : Entity), p.val.store.get i = some e → q.val.store.get i = some f →
        e.val.archive = none → ∀ bm', remainingOf bm' f.val.line = remainingOf bm' e.val.line := by
  intro hall
  cases h : close week closeNow 50 closeFoldPlan with
  | error x =>
    have hw := the_fold_facts_on_the_loaded_witness
    unfold foldClosed at hw; rw [h] at hw; cases hw
  | ok q =>
    obtain ⟨⟨e, f, he, hf, hp1⟩, -⟩ := fold_facts h
    obtain ⟨-, -, -, hre, -, hrf, ha, -, -⟩ := foldFacts_eq hp1
    have := hall week closeNow 50 closeFoldPlan q h _ e f he hf (archive_none_of_toNat ha) 50
    omega

/-- A line a close files: its closed region, a box the row takes, not recurring, not
routed as overdue, not a wall. -/
theorem closeAct_file_facts {g : Grain} {now : Day} {p : PlanCore} {s : Skel} {r : Region}
    (h : closeAct g now p s = .file r) :
    closedRegionOf g now p s.doc = some r ∧ (closePolicy g).takes s.status = true ∧
      s.recurring = false ∧ ¬ ((closePolicy g).overdue = .toBacklogOverdue ∧ s.overdue now = true) ∧
      s.wallAhead now = none := by
  unfold closeAct at h
  split at h
  · cases h
  · rename_i r' hr
    split at h
    · cases h
    · rename_i htk
      split at h
      · rw [(closePolicy_exemptions g).1] at h; simp [exemptAct] at h
      · rename_i hrec
        split at h
        · cases h
        · rename_i hov
          split at h
          · rename_i b _; cases b <;> simp [(closePolicy_exemptions g).2, exemptAct] at h
          · rename_i hw
            injection h with h
            subst h
            exact ⟨hr, by simpa using htk, by simpa using hrec, hov, hw⟩

/-- **`close_files_a_taken_line_into_closeTo`, refuted since B3's repair.**  `^c3`, a
line the week row takes, is dropped with its parent and stays in 2026-W36, not in
`closeTo week now`.  What holds is `close_files_a_taken_line_it_does_not_drop_into_closeTo`
and `close_week_drops_a_child_with_its_parent` (Close.lean). -/
theorem a_dropped_child_is_not_filed_into_closeTo :
    ¬ ∀ (g : Grain) (now : Day) (bm : Nat) (p q : WfPlan), close g now bm p = .ok q →
      ∀ {i : Id} {e f : Entity}, p.val.store.get i = some e → q.val.store.get i = some f →
        ∀ {r : Region}, closeAct g now p.val e.val.skel = .file r →
          docRegion q.val f.val.live.doc = some (closeTo g now) ∧
            docKindAt q.val f.val.live.doc = kindOfGrain (coarsen g) ∧
            f.val.skel = skelAfter g r f.val.live.doc .none e.val.skel := by
  intro hall
  cases h : close week closeNow 50 closeFoldPlan with
  | error x =>
    have hw := the_fold_facts_on_the_loaded_witness
    unfold foldClosed at hw; rw [h] at hw; cases hw
  | ok q =>
    obtain ⟨-, -, ⟨e, f, he, hf, hc3⟩, -⟩ := fold_facts h
    obtain ⟨hfl, -, -, -, -, -, -, -, hreg⟩ := foldFacts_eq hc3
    obtain ⟨r, hr⟩ := filesLine_iff.1 (toNat_eq_one hfl)
    have := (hall week closeNow 50 closeFoldPlan q h he hf hr).1
    have hno := toNat_eq_zero hreg
    rw [this] at hno
    simp at hno

/-- **`close_week_merges_a_standing_record`, refuted since B3's repair.**  `^c5` has a
standing `# Demoted` record and the week row takes it, and it is dropped with its
parent — `[~]`, not a `[-]` record.  What holds is
`close_week_merges_a_standing_record_it_does_not_drop` (Close.lean). -/
theorem a_dropped_child_keeps_its_record_unmerged :
    ¬ ∀ (now : Day) (bm : Nat) (p q : WfPlan), close week now bm p = .ok q →
      ∀ {i : Id} {e f : Entity}, p.val.store.get i = some e → q.val.store.get i = some f →
        ∀ {r : Region}, closeAct week now p.val e.val.skel = .file r → ∀ {t : Tomb},
          e.val.archive = some t →
          f.val.archive.map Tomb.line = some e.val.line ∧ f.val.status = .demoted ∧
            f.val.stamps = mergeStamps (stampsOfLine t.line) e.val.stamps
              (.week (Cal.isoOf (7 * r.ix)).week) ∧
            (ownsEstimate e.val.line = true → f.val.line = Field.setDemoted f.val.stamps e.val.line) ∧
            ∀ bm', ownsEstimate e.val.line = false →
              recordedEst bm' t.line ≤ remainingOf bm' f.val.line ∧
                remainingOf bm' e.val.line ≤ remainingOf bm' f.val.line := by
  intro hall
  cases h : close week closeNow 50 closeFoldPlan with
  | error x =>
    have hw := the_fold_facts_on_the_loaded_witness
    unfold foldClosed at hw; rw [h] at hw; cases hw
  | ok q =>
    obtain ⟨-, -, -, ⟨e, f, he, hf, hc5⟩⟩ := fold_facts h
    obtain ⟨hfl, -, -, -, -, -, ha, hdr, -⟩ := foldFacts_eq hc5
    obtain ⟨r, hr⟩ := filesLine_iff.1 (toNat_eq_one hfl)
    have hsome := toNat_eq_one ha
    cases hat : e.val.archive with
    | none => rw [hat] at hsome; cases hsome
    | some t =>
      have hst := (hall closeNow 50 closeFoldPlan q h he hf hr hat).2.1
      have hdrop : f.val.status = .settled .dropped := by simpa using toNat_eq_one hdr
      rw [hdrop] at hst
      cases hst

/-- `^c5`'s hypotheses for the two D8 laws: filed, so in a closed region with a box the
week row takes, not recurring, not overdue; a point due on or after Monday. -/
theorem c5_dated_facts {q : WfPlan} (h : close week closeNow 50 closeFoldPlan = .ok q) :
    ∃ e f r m, closeFoldPlan.val.store.get "c5".toList = some e ∧ q.val.store.get "c5".toList = some f ∧
      closedRegionOf week closeNow closeFoldPlan.val e.val.live.doc = some r ∧
      (closePolicy week).takes e.val.status = true ∧ e.val.recur = Field.Recur.none ∧
      e.val.shape = Field.Shape.point m ∧ closeNow ≤ m.day ∧ e.val.skel.overdue closeNow = false ∧
      f.val.status = .settled .dropped := by
  obtain ⟨-, -, -, ⟨e, f, he, hf, hc5⟩⟩ := fold_facts h
  obtain ⟨hfl, -, -, -, -, -, -, hdr, -⟩ := foldFacts_eq hc5
  obtain ⟨r, hr⟩ := filesLine_iff.1 (toNat_eq_one hfl)
  obtain ⟨hreg, htk, _, hov, _⟩ := closeAct_file_facts hr
  have hd := the_fold_witness_links_and_dates.2.1
  rw [he] at hd
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨hrec, hsh⟩ := hd
  cases hs : e.val.shape with
  | point m =>
    rw [hs] at hsh
    refine ⟨e, f, r, m, he, hf, hreg, htk, by simpa using hrec, hs, by simpa using hsh, ?_,
      by simpa using toNat_eq_one hdr⟩
    cases ho : e.val.skel.overdue closeNow with
    | false => rfl
    | true => exact absurd ⟨rfl, ho⟩ hov
  | none => rw [hs] at hsh; cases hsh
  | interval _ _ => rw [hs] at hsh; cases hsh
  | window _ _ => rw [hs] at hsh; cases hsh

/-- **`close_week_files_a_dated_line_keeping_its_date`, refuted since B3's repair.**
`^c5`, a point-dated line of a closed week that is not past due, is dropped with its
parent: `[~]`, not a `[-]` record.  What holds is
`close_week_files_a_dated_line_it_does_not_drop_keeping_its_date` (Close.lean). -/
theorem a_dropped_dated_child_is_not_filed_as_a_record :
    ¬ ∀ (now : Day) (bm : Nat) (p q : WfPlan), close week now bm p = .ok q →
      ∀ {i : Id} {e f : Entity}, p.val.store.get i = some e → q.val.store.get i = some f →
        ∀ {r : Region}, closedRegionOf week now p.val e.val.live.doc = some r →
        (closePolicy week).takes e.val.status = true → e.val.recur = Field.Recur.none →
        ∀ {m : Field.Moment}, e.val.shape = Field.Shape.point m → e.val.skel.overdue now = false →
        docRegion q.val f.val.live.doc = some (closeTo week now) ∧
          docKindAt q.val f.val.live.doc = .month ∧
          f.val.status = .demoted ∧ f.val.archive.map Tomb.line = some e.val.line ∧
          Field.Stamp.week (Cal.isoOf (7 * r.ix)).week ∈ f.val.stamps ∧
          f.val.shape = e.val.shape := by
  intro hall
  cases h : close week closeNow 50 closeFoldPlan with
  | error x =>
    have hw := the_fold_facts_on_the_loaded_witness
    unfold foldClosed at hw; rw [h] at hw; cases hw
  | ok q =>
    obtain ⟨e, f, r, m, he, hf, hreg, htk, hrec, hsh, _, hov, hdrop⟩ := c5_dated_facts h
    have hst := (hall closeNow 50 closeFoldPlan q h he hf hreg htk hrec hsh hov).2.2.1
    rw [hdrop] at hst
    cases hst

/-- **`close_week_demotes_a_not_yet_due_line_keeping_its_date`, refuted since B3's
repair** — D8's law stated without §6.3's child rule.  `^c5` is not yet due and is
unfinished at the close, and it is dropped with the parent the close files, as §6.3
drops any unfinished child.  What holds is
`close_week_demotes_a_not_yet_due_line_it_does_not_drop_keeping_its_date` (Close.lean). -/
theorem a_not_yet_due_child_is_dropped_with_its_parent :
    ¬ ∀ (now : Day) (bm : Nat) (p q : WfPlan), close week now bm p = .ok q →
      ∀ {i : Id} {e f : Entity}, p.val.store.get i = some e → q.val.store.get i = some f →
        ∀ {r : Region}, closedRegionOf week now p.val e.val.live.doc = some r →
        (closePolicy week).takes e.val.status = true → e.val.recur = Field.Recur.none →
        ∀ {m : Field.Moment}, e.val.shape = Field.Shape.point m → now ≤ m.day →
        docRegion q.val f.val.live.doc = some (closeTo week now) ∧
          docKindAt q.val f.val.live.doc = .month ∧
          f.val.status = .demoted ∧ f.val.archive.map Tomb.line = some e.val.line ∧
          Field.Stamp.week (Cal.isoOf (7 * r.ix)).week ∈ f.val.stamps ∧
          f.val.shape = e.val.shape := by
  intro hall
  cases h : close week closeNow 50 closeFoldPlan with
  | error x =>
    have hw := the_fold_facts_on_the_loaded_witness
    unfold foldClosed at hw; rw [h] at hw; cases hw
  | ok q =>
    obtain ⟨e, f, r, m, he, hf, hreg, htk, hrec, hsh, hnot, _, hdrop⟩ := c5_dated_facts h
    have hst := (hall closeNow 50 closeFoldPlan q h he hf hreg htk hrec hsh hnot).2.2.1
    rw [hdrop] at hst
    cases hst

/-- **`close_keeps_source_order` without the fold's clause, refuted.**  `^p1` and its
subtask `^c1` are taken from 2026-W36 by one action, `file`, `^p1` above; the child
fold drops `^c1` and files `^p1`, so they end in different files.  What holds is
`close_keeps_source_order` as re-proved at B3's repair (Close.lean): "the same action"
includes whether the fold drops the line. -/
theorem a_dropped_child_and_its_filed_parent_part_ways :
    ¬ ∀ (g : Grain) (now : Day) (bm : Nat) (p q : WfPlan), close g now bm p = .ok q →
      ∀ {i j : Id} {ei ej : Entity}, p.val.store.get i = some ei → p.val.store.get j = some ej →
        closeAct g now p.val ei.val.skel ≠ .stay →
        closeAct g now p.val ej.val.skel = closeAct g now p.val ei.val.skel →
        ei.val.live.doc = ej.val.live.doc →
        (closeAct g now p.val ei.val.skel ≠ .carry → (closePolicy g).landing = .sameSection →
          sectionAt p.val ei.val.live = sectionAt p.val ej.val.live) →
        ei.val.live.rank < ej.val.live.rank →
        ∃ fi fj, q.val.store.get i = some fi ∧ q.val.store.get j = some fj ∧
          fi.val.live.doc = fj.val.live.doc ∧ fi.val.live.rank < fj.val.live.rank := by
  intro hall
  cases h : close week closeNow 50 closeFoldPlan with
  | error x =>
    have hw := the_fold_facts_on_the_loaded_witness
    unfold foldClosed at hw; rw [h] at hw; cases hw
  | ok q =>
    obtain ⟨⟨ei, fi0, hei, hfi0, hp1⟩, -⟩ := fold_facts h
    obtain ⟨hfl, -, -, -, -, -, -, -, -⟩ := foldFacts_eq hp1
    obtain ⟨r, hr⟩ := filesLine_iff.1 (toNat_eq_one hfl)
    have hl := the_fold_witness_links_and_dates.2.2.2
    obtain ⟨hpair, hdocs⟩ := hl
    cases hej : closeFoldPlan.val.store.get "c1".toList with
    | none => rw [hei, hej] at hpair; cases hpair
    | some ej =>
      rw [hei, hej] at hpair
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpair
      obtain ⟨⟨hact, hdoc⟩, hlt⟩ := hpair
      obtain ⟨fi, fj, hfi, hfj, hd, _⟩ := hall week closeNow 50 closeFoldPlan q h hei hej
        (by rw [hr]; simp) hact hdoc (fun _ hl => absurd hl (by decide)) hlt
      unfold foldClosed at hdocs
      rw [h] at hdocs
      simp only [Option.some.injEq, hfi, hfj, Option.map_some, ne_eq, decide_eq_true_eq] at hdocs
      exact hdocs (by rw [hd])

/-- **`closeReport_names_the_destination_of_now`, refuted since B3's repair.**  Its third
clause names `closeTo g now` for every entry that is neither a carry nor an overdue
move; `^c3`'s entry is `dropIntoParent`, and the line stays in 2026-W36.  What holds
is `closeReport_names_each_lines_destination` (Report.lean). -/
theorem a_dropped_child_is_reported_where_it_stays :
    ¬ ∀ (g : Grain) (now : Day) (bm : BlockMin) (p q : WfPlan), close g now bm.val p = .ok q →
      ∀ {x : CloseEntry}, x ∈ closeReport g now bm p.val →
        (x.did = .carry → docRegion q.val x.dst = some (regionOf week now)) ∧
          (x.did = .moveOverdue → docKindAt q.val x.dst = .backlog ∧ docRegion q.val x.dst = none) ∧
          (x.did ≠ .carry → x.did ≠ .moveOverdue → docRegion q.val x.dst = some (closeTo g now)) := by
  intro hall
  cases h : close week closeNow 50 closeFoldPlan with
  | error x =>
    have hw := the_fold_facts_on_the_loaded_witness
    unfold foldClosed at hw; rw [h] at hw; cases hw
  | ok q =>
    obtain ⟨-, -, ⟨e, f, he, hf, hc3⟩, -⟩ := fold_facts h
    obtain ⟨-, -, -, -, -, -, -, -, hreg⟩ := foldFacts_eq hc3
    have hrep := the_fold_witness_links_and_dates.2.2.1
    obtain ⟨x, hx, hxs⟩ := Option.map_eq_some_iff.mp hrep
    have hmem := List.mem_of_find?_eq_some hx
    have hid : x.id = "c3".toList := by simpa using List.find?_some hx
    simp only [Prod.mk.injEq] at hxs
    obtain ⟨hdid, hdst⟩ := hxs
    have hq := (hall week closeNow blockMin50 closeFoldPlan q h hmem).2.2 (by rw [hdid]; decide)
      (by rw [hdid]; decide)
    obtain ⟨-, e', f', he', hf', -, hd, -⟩ := closeReport_agrees_with_close_stamping_or_merging
      (bm := blockMin50) h hmem
    rw [hid, hf] at hf'
    injection hf' with hf'
    subst hf'
    rw [← hd] at hq
    have hno := toNat_eq_zero hreg
    rw [hq] at hno
    simp at hno

/-- **`close_week_folds_dropped_children_by_max`'s hypotheses are satisfiable, in both
directions**: `b = true` is a stale parent the fold lifts (`^p1`, 100 < 150), `b = false`
one that covers its children (`^p2`, 100 ≤ 300). -/
theorem close_week_folds_dropped_children_by_max_is_not_vacuous (b : Bool) :
    ∃ (now : Day) (bm : Nat) (p q : WfPlan) (i : Id) (e f : Entity) (r : Region),
      close week now bm p = .ok q ∧ p.val.store.get i = some e ∧ q.val.store.get i = some f ∧
        closeAct week now p.val e.val.skel = .file r ∧ dropsInto week now p.val i = none ∧
        decide (remainingOf bm (carriedLine e) < foldedMinutes week now bm p.val i) = b := by
  cases h : close week closeNow 50 closeFoldPlan with
  | error x =>
    have hw := the_fold_facts_on_the_loaded_witness
    unfold foldClosed at hw; rw [h] at hw; cases hw
  | ok q =>
    obtain ⟨⟨e1, f1, he1, hf1, hp1⟩, ⟨e2, f2, he2, hf2, hp2⟩, -⟩ := fold_facts h
    obtain ⟨hfl1, hnd1, hfm1, -, hc1, -, -, -, -⟩ := foldFacts_eq hp1
    obtain ⟨hfl2, hnd2, hfm2, -, hc2, -, -, -, -⟩ := foldFacts_eq hp2
    obtain ⟨r1, hr1⟩ := filesLine_iff.1 (toNat_eq_one hfl1)
    obtain ⟨r2, hr2⟩ := filesLine_iff.1 (toNat_eq_one hfl2)
    have hn1 : dropsInto week closeNow closeFoldPlan.val "p1".toList = none := by
      simpa using toNat_eq_one hnd1
    have hn2 : dropsInto week closeNow closeFoldPlan.val "p2".toList = none := by
      simpa using toNat_eq_one hnd2
    cases b
    · exact ⟨_, _, _, _, _, e2, f2, r2, h, he2, hf2, hr2, hn2, by rw [hc2, hfm2]; decide⟩
    · exact ⟨_, _, _, _, _, e1, f1, r1, h, he1, hf1, hr1, hn1, by rw [hc1, hfm1]; decide⟩

/-- **`close_week_drops_a_child_with_its_parent`'s and
`close_week_keeps_a_dropped_childs_remaining_in_its_parents_record`'s hypotheses are
satisfiable**: `^c3` is dropped into `^p2`. -/
theorem close_week_drops_a_child_with_its_parent_is_not_vacuous :
    ∃ (now : Day) (bm : Nat) (p q : WfPlan) (i j : Id) (e f fp : Entity),
      close week now bm p = .ok q ∧ p.val.store.get j = some e ∧ q.val.store.get j = some f ∧
        q.val.store.get i = some fp ∧ dropsInto week now p.val j = some i := by
  cases h : close week closeNow 50 closeFoldPlan with
  | error x =>
    have hw := the_fold_facts_on_the_loaded_witness
    unfold foldClosed at hw; rw [h] at hw; cases hw
  | ok q =>
    obtain ⟨-, ⟨e2, f2, _, hf2, _⟩, ⟨e3, f3, he3, hf3, _⟩, -⟩ := fold_facts h
    have hd : dropsInto week closeNow closeFoldPlan.val "c3".toList = some "p2".toList := by
      have := the_fold_on_the_loaded_witness
      simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq] at this
      exact this.2.2.2.2.2.1.1
    exact ⟨_, _, _, _, _, _, e3, f3, f2, h, he3, hf3, hf2, hd⟩


/-! ## Stage 4 final, repair (2026-09-13): the mixed pair's order, and `NhMm` in the fold

Two defects an independent verification found in step 4.  (Defect 2) the mixed pair —
one line the fold drops, one it files, taken from one file by one action — had no
order law once `close_keeps_source_order` gained `hfold`; `Close.lean`'s
`close_keeps_source_order_across_the_fold` states it over the sites the two leave in
the source file, and it is decided below on the fold witness's `^p1`/`^c1`, the pair
`a_dropped_child_and_its_filed_parent_part_ways` separates.  (Defect 3) the stage-one
reader `unitValue` did not read `NhMm`, so a `2h30m` child counted `0` in the fold and
its parent's record lost 150 minutes while the report (`estMinutes`) and the Rust
read them; `unitValue_renderDur` (Line.lean) is the law, `closeHmWitness` the loaded
plan (each decision probed alone under an 8 GB cap first). -/

set_option maxRecDepth 40000 in
/-- **The mixed pair on the loaded witness**: the fold files `^p1` and drops `^c1`; after
the close `^p1`'s tombstone stands in `^c1`'s file, above it, as `^p1` stood above
`^c1`. -/
theorem the_mixed_pair_keeps_its_order_on_the_loaded_witness :
    (foldFxOf week closeNow 50 closeFoldPlan.val "p1".toList).isDrop = false ∧
      (foldFxOf week closeNow 50 closeFoldPlan.val "c1".toList).isDrop = true ∧
      foldClosed (fun q => match q.val.store.get "p1".toList, q.val.store.get "c1".toList with
        | some fp, some fc =>
          fp.val.archiveSite.map (fun t => decide (t.doc = fc.val.live.doc ∧ t.rank < fc.val.live.rank))
        | _, _ => none) = some (some true) := by
  decide

/-- **`close_keeps_source_order_across_the_fold`'s hypotheses are satisfiable**: `^p1`
filed and `^c1` dropped, one action, one file, `^p1` above. -/
theorem close_keeps_source_order_across_the_fold_is_not_vacuous :
    ∃ (g : Grain) (now : Day) (bm : Nat) (p q : WfPlan) (i j : Id) (ei ej : Entity),
      close g now bm p = .ok q ∧ p.val.store.get i = some ei ∧ p.val.store.get j = some ej ∧
        closeAct g now p.val ej.val.skel = closeAct g now p.val ei.val.skel ∧
        (foldFxOf g now bm p.val i).isDrop = false ∧ (foldFxOf g now bm p.val j).isDrop = true ∧
        ei.val.live.doc = ej.val.live.doc ∧ ei.val.live.rank < ej.val.live.rank := by
  cases h : close week closeNow 50 closeFoldPlan with
  | error x =>
    have hw := the_fold_facts_on_the_loaded_witness
    unfold foldClosed at hw; rw [h] at hw; cases hw
  | ok q =>
    obtain ⟨⟨ei, _, hei, _, _⟩, -⟩ := fold_facts h
    obtain ⟨hpair, -⟩ := the_fold_witness_links_and_dates.2.2.2
    obtain ⟨hxi, hxj, -⟩ := the_mixed_pair_keeps_its_order_on_the_loaded_witness
    cases hej : closeFoldPlan.val.store.get "c1".toList with
    | none => rw [hei, hej] at hpair; cases hpair
    | some ej =>
      rw [hei, hej] at hpair
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpair
      obtain ⟨⟨hact, hdoc⟩, hlt⟩ := hpair
      exact ⟨week, closeNow, 50, closeFoldPlan, q, _, _, ei, ej, h, hei, hej, hact, hxi, hxj, hdoc, hlt⟩

/-- 2026-W36 with a `6b` milestone whose two subtasks are `5h` and `2h30m`, and
September with §4.3's two sections. -/
def closeHmWitness : List ReqDoc :=
  [⟨"week/2026-W36.md", some closeW36,
     ["# Milestones".toList,
      "- [ ] 6b Parent project ^p1".toList,
      "# Tasks".toList,
      "- [ ] 5h Part one @p1 ^c1".toList,
      "- [ ] 2h30m Part two @p1 ^c2".toList]⟩,
   ⟨"month/2026-09.md", some closeM09, ["# Outcomes".toList, "# Demoted".toList]⟩]

set_option maxRecDepth 40000 in
/-- **An `NhMm` child is folded at its minutes, on a loaded plan.**  At a 50-minute
block `^p1` reads 300 and its dropped subtasks `300 + 150`; its record carries §6.4's
`max`, `est:9b`.  Before the repair `2h30m` read `0` and the record was the line with
only its stamp — 150 minutes of open work gone (defect 3). -/
theorem the_week_close_folds_an_hours_and_minutes_child :
    closedFileLines week closeHmWitness = some
      [["# Milestones".toList,
        "- [-] 6b Parent project ^p1".toList,
        "# Tasks".toList,
        "- [~] 5h Part one @p1 ^c1".toList,
        "- [~] 2h30m Part two @p1 ^c2".toList],
       ["# Outcomes".toList, "# Demoted".toList,
        "- [-] 6b Parent project est:9b demoted:W36 ^p1".toList]] := by
  decide

/-! ## Stage 5 step 1: §6.4's `remaining` and §5.4's series head, on a loaded plan

`Tree.lean` defines both and proves their laws over every well-formed plan.  Everything
below is decided on one small `backlog.md`, loaded through `loadPlan` exactly as the host
hands it over, so each rule is seen **firing** on what the boundary builds, and each of
`Goals.lean`'s three §6.4 rows is refuted as written on the same lines.  At a 60-minute
block:

* `^a1` `2b … est:30m` — the `est:` key wins over the leading estimate: 30;
* `^a2` `45m` — no key, the leading estimate: 45;
* `^p1`, no estimate, children `^c1` `30m` and `^c2` `20m` — the sum: 50;
* `^w1` `dur:30m` only — fork-point `Item::own_remaining`'s third slot: 30;
* `^d1` `[x] 1b … est:40m` and `^d2` `[x] 25m` — closed, so `Some(0)`: 0;
* `^n1`, nothing anywhere — `none`, read as 0;
* `## series:vols` `[x] ^v1`, `[ ] ^v2`, `[ ] ^v3` — the head skips the settled `^v1`:
  `^v2`; `## series:read` holds only a settled `^r1`: no head. -/

def treeWitness : List ReqDoc :=
  [⟨"backlog.md", none,
     ["# Untied".toList,
      "- [ ] 2b Key wins est:30m ^a1".toList,
      "- [ ] 45m Lead only ^a2".toList,
      "- [ ] Parent with no estimate ^p1".toList,
      "- [ ] 30m Child one @p1 ^c1".toList,
      "- [ ] 20m Child two @p1 ^c2".toList,
      "- [x] 1b Done with a key est:40m ^d1".toList,
      "- [x] 25m Done with a lead ^d2".toList,
      "- [ ] Watch the talk dur:30m ^w1".toList,
      "- [ ] No estimate at all ^n1".toList,
      "## series:vols".toList,
      "- [x] 1b Vol 1 ^v1".toList,
      "- [ ] 1b Vol 2 ^v2".toList,
      "- [ ] 1b Vol 3 ^v3".toList,
      "## series:read".toList,
      "- [x] 1b Old volume ^r1".toList]⟩]

set_option maxRecDepth 40000 in
/-- **The rollup witness loads.** -/
theorem the_tree_witness_loads : loadsOk treeWitness = true := by decide

/-- The loaded rollup witness.  Total by `the_tree_witness_loads`: the error branch is
refuted, not defaulted. -/
def treePlan : WfPlan :=
  match h : loadPlan treeWitness with
  | .ok p => p
  | .error _ => absurd the_tree_witness_loads (by simp [loadsOk, h])

/-- A Done or Dropped entity (fork-point `State::is_closed`). -/
def settledB (e : Entity) : Bool :=
  match e.val.status with
  | .settled _ => true
  | _          => false

/-- What the §6.4 laws assume of an id, read off a plan: its `est:` key, its leading
estimate, its `dur:`, and whether it is settled. -/
def estSlotsAt (p : PlanCore) (i : Id) :
    Option (Option Field.Dur × Option Field.Dur × Option Field.Dur × Bool) :=
  (p.store.get i).map (fun e =>
    (Field.viewEstKey e.val.line, Field.estLeadOf e.val.line, Field.viewDur e.val.line, settledB e))

set_option maxRecDepth 40000 in
/-- **§6.4 row 1 fires on a loaded plan: an `est:` key wins over a leading estimate.**
`^a1` writes both, `2b` and `est:30m`; its remaining is 30, not 120. -/
theorem remaining_reads_the_est_key_over_the_leading_estimate_on_a_loaded_plan :
    estSlotsAt treePlan.val "a1".toList =
        some (some (.simple 30 .minutes), some (.simple 2 .blocks), none, false) ∧
      remainingMin 60 treePlan "a1".toList = 30 := by
  decide

set_option maxRecDepth 40000 in
/-- **§6.4 row 2 fires on a loaded plan: with no key, the leading estimate.** -/
theorem remaining_reads_the_leading_estimate_on_a_loaded_plan :
    estSlotsAt treePlan.val "a2".toList = some (none, some (.simple 45 .minutes), none, false) ∧
      remainingMin 60 treePlan "a2".toList = 45 := by
  decide

set_option maxRecDepth 40000 in
/-- **§6.4 row 3 fires on a loaded plan: a parent with no estimate sums two children.**
The children are read off the line (`@p1`, D6) and listed in the store's order. -/
theorem remaining_sums_two_children_on_a_loaded_plan :
    estSlotsAt treePlan.val "p1".toList = some (none, none, none, false) ∧
      childrenOf treePlan.val "p1".toList = ["c2".toList, "c1".toList] ∧
      remainingMin 60 treePlan "p1".toList = 50 := by
  decide

set_option maxRecDepth 40000 in
/-- **The fork point's `dur:` row fires on a loaded plan.**  `^w1` writes no estimate
and has no children; its remaining is its `dur:`. -/
theorem remaining_reads_dur_on_a_loaded_plan :
    estSlotsAt treePlan.val "w1".toList = some (none, none, some (.simple 30 .minutes), false) ∧
      childrenOf treePlan.val "w1".toList = [] ∧
      remainingMin 60 treePlan "w1".toList = 30 := by
  decide

set_option maxRecDepth 40000 in
/-- **A settled line has nothing remaining, on a loaded plan**, whichever estimate it
writes: `^d1` an `est:` key, `^d2` a leading estimate. -/
theorem remaining_of_a_settled_line_is_zero_on_a_loaded_plan :
    estSlotsAt treePlan.val "d1".toList =
        some (some (.simple 40 .minutes), some (.simple 1 .blocks), none, true) ∧
      remainingMin 60 treePlan "d1".toList = 0 ∧
      estSlotsAt treePlan.val "d2".toList = some (none, some (.simple 25 .minutes), none, true) ∧
      remainingMin 60 treePlan "d2".toList = 0 := by
  decide

set_option maxRecDepth 40000 in
/-- **The edges: no estimate anywhere is `none`** (fork-point `Tree::remaining`'s
`None`), read as 0 by `remainingMin`; an id the plan does not hold is `none` too. -/
theorem remaining_is_none_without_an_estimate_on_a_loaded_plan :
    remainingOpt 60 treePlan.val "n1".toList = none ∧ remainingMin 60 treePlan "n1".toList = 0 ∧
      remainingOpt 60 treePlan.val "zz".toList = none := by
  decide

set_option maxRecDepth 40000 in
/-- **§5.4 fires on a loaded plan: a settled head is skipped for the next open member.**
`^v1` is `[x]` and sits in `## series:vols`, so the head is `^v2`.  And both edges: a
series whose only member is settled has no head, and neither does a name no section
carries. -/
theorem the_series_head_skips_a_settled_member_on_a_loaded_plan :
    (treePlan.val.store.get "v1".toList).map (fun e => (settledB e, seriesOf treePlan.val e.val.live)) =
        some (true, some "vols".toList) ∧
      seriesHead treePlan 0 "vols".toList = some "v2".toList ∧
      seriesHead treePlan 0 "read".toList = none ∧
      seriesHead treePlan 0 "nope".toList = none := by
  decide

/-- **`Goals.lean`'s `remaining_is_the_est_key_when_set`, refuted as written.**  Its
statement, quantifier for quantifier, fails at `^d1`: `[x] 1b … est:40m` has an `est:`
key and nothing remaining, because fork-point `Tree::remaining_inner` answers `Some(0)`
for a closed item before it reads an estimate.  What holds is
`remaining_is_the_est_key_when_set_and_unsettled`. -/
theorem remaining_is_not_the_est_key_on_a_settled_line :
    ¬ ∀ (bm : Nat) (p : WfPlan) (i : Id) (e : Entity) (d : Field.Dur),
      p.val.store.get i = some e → Field.viewEstKey e.val.line = some d →
      remainingMin bm p i = Field.Dur.minutes bm d := by
  intro hall
  have hw := remaining_of_a_settled_line_is_zero_on_a_loaded_plan
  simp only [estSlotsAt, Option.map_eq_some_iff, Prod.mk.injEq] at hw
  obtain ⟨⟨e, hg, hk, -, -, -⟩, h0, -⟩ := hw
  have h := hall 60 treePlan _ e _ hg hk
  rw [h0] at h
  simp [Field.Dur.minutes] at h

/-- **`Goals.lean`'s `remaining_falls_back_to_the_leading_estimate`, refuted as
written.**  It fails at `^d2`: `[x] 25m` has no key, a leading estimate, and nothing
remaining.  What holds is `remaining_falls_back_to_the_leading_estimate_when_unsettled`. -/
theorem remaining_does_not_fall_back_to_the_leading_estimate_on_a_settled_line :
    ¬ ∀ (bm : Nat) (p : WfPlan) (i : Id) (e : Entity) (d : Field.Dur),
      p.val.store.get i = some e → Field.viewEstKey e.val.line = Option.none →
      (Field.viewFields e.val.line).estLead = some d →
      remainingMin bm p i = Field.Dur.minutes bm d := by
  intro hall
  have hw := remaining_of_a_settled_line_is_zero_on_a_loaded_plan
  simp only [estSlotsAt, Option.map_eq_some_iff, Prod.mk.injEq] at hw
  obtain ⟨-, -, ⟨e, hg, hk, hl, -, -⟩, h0⟩ := hw
  have h := hall 60 treePlan _ e _ hg hk hl
  rw [h0] at h
  simp [Field.Dur.minutes] at h

set_option maxRecDepth 40000 in
/-- **`Goals.lean`'s `remaining_sums_the_children`, refuted as written.**  It fails at
`^w1`: no key, no leading estimate, no children — the sum is 0 — and `dur:30m`, which
fork-point `Item::own_remaining` reads before the children.  (A settled parent over an
open child refutes it too, by `remaining_of_a_settled_item_is_zero`.)  What holds is
`remaining_sums_the_children_when_unsettled_with_no_dur`, with
`remaining_falls_back_to_dur_when_unsettled` for the row §6.4 does not write. -/
theorem remaining_does_not_sum_the_children_over_a_dur :
    ¬ ∀ (bm : Nat) (p : WfPlan) (i : Id) (e : Entity),
      p.val.store.get i = some e → Field.viewEstKey e.val.line = Option.none →
      (Field.viewFields e.val.line).estLead = Option.none →
      remainingMin bm p i
        = (p.val.store.dom.filter (fun j => parentStep p.val j == some i)).foldl
            (fun a j => a + remainingMin bm p j) 0 := by
  intro hall
  have hw := remaining_reads_dur_on_a_loaded_plan
  simp only [estSlotsAt, Option.map_eq_some_iff, Prod.mk.injEq] at hw
  obtain ⟨⟨e, hg, hk, hl, -, -⟩, -, -⟩ := hw
  have h := hall 60 treePlan _ e hg hk hl
  revert h
  decide

/-! ## Stage 5 step 2: §7.1's `k` and `p`, §7.2's table and §7.4's hysteresis, on a loaded plan

`rootK` is fork-point `Tree::root_priority` (`Priority.lean`): the root's written `!k`,
else §16's `default_priority`.  Every decision below reads `k` off a plan the loader
built — `parentTreePlan` (D6's tree: `^t1` under `^m1` under `^O1 !1`, `^x2` under the
midterm `^x1` under `^O3 !3`) and `treePlan` (`^a1`, a root with no `!k`) — and the bin
off Arith's ladder at a 60-minute remaining with §16's `safety = 13/10`, a need of 78
minutes, never rounded (R1).  Each was probed alone under an 8 GB cap first (README
"Stage 5 step 2"). -/

set_option maxRecDepth 40000 in
/-- **§7.1's `k = root_priority` feeds `p` on a loaded plan.**  `^t1` climbs to `^O1`'s
`!1` and `^x2` to `^O3`'s `!3`; at 200 minutes available a need of 78 is `u = 0.39`, bin
`+1`, so `p` is `1 + 1 = 2` and `3 + 1 = 4`. -/
theorem prio_reads_the_root_priority_on_a_loaded_plan :
    rootK parentTreePlan.val specDefaultPrio "t1".toList = 1 ∧
      rootK parentTreePlan.val specDefaultPrio "x2".toList = 3 ∧
      binOfScaledQ Arith.defaultBins Arith.safety 60 (Arith.posOfNat 200) = .plus 1 ∧
      prio (rootK parentTreePlan.val specDefaultPrio "t1".toList)
          (binOfScaledQ Arith.defaultBins Arith.safety 60 (Arith.posOfNat 200)) = 2 ∧
      prio (rootK parentTreePlan.val specDefaultPrio "x2".toList)
          (binOfScaledQ Arith.defaultBins Arith.safety 60 (Arith.posOfNat 200)) = 4 := by
  decide

set_option maxRecDepth 40000 in
/-- **A root with no `!k` takes the default, on a loaded plan** — the other direction:
`^a1` has neither a parent nor a `!k`, and its `k` is §16's `3`. -/
theorem a_root_without_k_takes_the_default_on_a_loaded_plan :
    (treePlan.val.store.get "a1".toList).map (fun e => (e.val.prio, e.val.parent)) =
        some (Option.none, Option.none) ∧
      rootK treePlan.val specDefaultPrio "a1".toList = 3 := by
  decide

set_option maxRecDepth 40000 in
/-- **HOT is `p = 0` whatever the root says, on a loaded plan.**  At exactly 78 minutes
available `u = 1`; `^x2`'s `k = 3` does not push it off the front. -/
theorem hot_is_zero_whatever_the_root_on_a_loaded_plan :
    binOfScaledQ Arith.defaultBins Arith.safety 60 (Arith.posOfNat 78) = .hot ∧
      prio (rootK parentTreePlan.val specDefaultPrio "x2".toList)
          (binOfScaledQ Arith.defaultBins Arith.safety 60 (Arith.posOfNat 78)) = 0 := by
  decide

set_option maxRecDepth 40000 in
/-- **§7.2's table and §7.4's hysteresis, on a loaded plan's `k`.**  `^x2` dated at bin
`+1` is raw `4`; yesterday's `6` holds it at `5`.  `^t1` with no pass is pure rank,
`1 + 2 = 3`, and no yesterday lets it through.  An optional is `5` whatever yesterday's
`7`.  An overdue line is `0` over any yesterday.  A wall is off the scale. -/
theorem the_rule_table_ranks_a_loaded_plan :
    finalPrio true (yesterdayOf? 6) (rootK parentTreePlan.val specDefaultPrio "x2".toList)
        ⟨false, false, false, false, false,
          some (binOfScaledQ Arith.defaultBins Arith.safety 60 (Arith.posOfNat 200))⟩ = some 5 ∧
      finalPrio true Option.none (rootK parentTreePlan.val specDefaultPrio "t1".toList)
        ⟨false, false, false, false, false, Option.none⟩ = some 3 ∧
      finalPrio true (yesterdayOf? 7) (rootK parentTreePlan.val specDefaultPrio "t1".toList)
        ⟨false, true, false, false, false, Option.none⟩ = some 5 ∧
      finalPrio true (yesterdayOf? 7) (rootK parentTreePlan.val specDefaultPrio "x2".toList)
        ⟨false, false, true, false, false,
          some (binOfScaledQ Arith.defaultBins Arith.safety 60 (Arith.posOfNat 200))⟩ = some 0 ∧
      finalPrio true (yesterdayOf? 7) (rootK parentTreePlan.val specDefaultPrio "x2".toList)
        ⟨true, false, false, false, false, Option.none⟩ = Option.none := by
  decide

set_option maxRecDepth 40000 in
/-- **§7.3's pass over a loaded plan's needs.**  `treePlan`'s `^a1` (30 minutes remaining)
and `^a2` (45) become R1's needs `39` and `59` (`needMin safety`, a ceiling).  `^a2` is
listed first and due on day 2, `^a1` due on day 1, over 60 minutes on day 1 and 30 on day 2
at level 3.  `^a1` is served first and reserves 39 of 60.  `^a2` then sees the 21 left on day 1
plus day 2's 30: it reserves 51 and reports 8 short. -/
theorem edf_serves_a_loaded_plans_needs_earliest_deadline_first :
    remainingMin 60 treePlan "a1".toList = 30 ∧ remainingMin 60 treePlan "a2".toList = 45 ∧
      (edfGrants Den.one [DayCapacity.ofLevels 1 [0, 0, 0, 60, 0, 0], DayCapacity.ofLevels 2 [0, 0, 0, 30, 0, 0]]
        [Deadline.ofRemaining Arith.safety (remainingMin 60 treePlan "a2".toList) 3 2,
         Deadline.ofRemaining Arith.safety (remainingMin 60 treePlan "a1".toList) 3 1]).map
        (fun g => (g.deadline.need, g.avail, g.reserved, g.shortfall 1)) = [(39, 60, 39, 0), (59, 51, 51, 8)] := by
  decide

/-! ## Stage 5 A2: a decimal on the wire is refused by its reader, not by the parser

APPENDED 2026-09-14 (stage-5 D9 track, step A2; design §5.1).  `JVal` gained
`dec`, so `jparse` reads `-3`, `1.5` and `1e3` (the refutation
`jparse_reads_what_the_fragment_had_no_type_for` in `Json.lean`).  What keeps the
request honest is the field's reader: every one wants `num`, and each match
already ended in a wildcard arm, so no arm was added and the refusal texts are the
ones a string or `null` already got — `getNat`'s `Natural number expected` for
`doc`, `min`, `period`, `rank`, `seed`, `grain` and `ix`, and `badBlockMin` for
`blockMin`.  Before A2 the same requests were `bad json: notAValue -`,
`bad json: expectedCommaOrBrace .` and the like; that change of text is the
behaviour row. -/

/-- **A request number that is not a natural is refused by the field's reader**,
and the same field carrying a natural reads (§5.8: bites, does not over-bite). -/
theorem a_request_number_that_is_not_a_nat_is_refused_by_its_reader :
    parseCmd (.obj [("op".toList, .str "est".toList), ("id".toList, .str "m1".toList),
        ("min".toList, .dec ⟨⟨true, 3, [], none⟩, rfl⟩)]) = .error "Natural number expected" ∧
    parseCmd (.obj [("op".toList, .str "move".toList), ("id".toList, .str "m1".toList),
        ("doc".toList, .dec ⟨⟨false, 1, [5], none⟩, rfl⟩)]) = .error "Natural number expected" ∧
    (parseClock (.obj [("blockMin".toList, .dec ⟨⟨false, 1, [5], none⟩, rfl⟩)])).map
      (fun c => c.now) = .error "badBlockMin" ∧
    parseRegion (.obj [("grain".toList, .dec ⟨⟨false, 1, [], some (false, 0, [])⟩, rfl⟩)])
      = .error "Natural number expected" ∧
    parseCmd (.obj [("op".toList, .str "est".toList), ("id".toList, .str "m1".toList),
        ("min".toList, .num 3)]) = .ok (.est "m1".toList 3) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **End to end at `respond`, over explicit `List Char` inputs** (the Json.lean
memory rule): a decimal at a key no reader reads is accepted, where it used to be
`bad json`; a leading zero is refused by name (gap 43); and a surrogate pair
parses, so the refusal is the reader's `object expected` for a top-level string,
not the parser's `surrogateEscape` (gap 42). -/
theorem respond_reads_a_decimal_and_a_surrogate_pair :
    respond ['{', '"', 'd', 'o', 'c', 's', '"', ':', '[', ']', ',', '"', 'x', '"', ':',
             '-', '0', '.', '5', '}']
      = jone "ok" (.obj [("docs".toList, .arr []), ("report".toList, jone "closes" (.arr []))]) ∧
    respond ['0', '0', '7'] = jsonErr "bad json: leadingZero" ∧
    respond ['"', '\\', 'u', 'd', '8', '3', 'd', '\\', 'u', 'd', 'e', '0', '0', '"']
      = jsonErr "object expected" :=
  ⟨rfl, rfl, rfl⟩


/-! ## Stage 5 D9 B4: the `tz` and `log` sections — the laws

APPENDED 2026-09-14 (stage 5, D9 track, step B4; design §6.1, §10, §14.2 row B4).  The definitions
sit after `run` (section "The `tz` and `log` sections"), because `respond` calls them; these are
their laws.

* **The op is beside the plan, never inside it.**  A request without `tz` and `log` is `run`
  (`a_request_without_tz_or_log_is_read_as_before`); a refused section refuses the request before
  the plan is loaded (`runWithLog_refuses_a_log_section_first`); an answered one is the `ok` object
  `run` built with `log` after `report` (`runWithLog_puts_the_log_after_the_report`, over
  `run_ok_shape`, which reads every path of `run`).
* **Every tail line is read by `Log.readLine` at its physical number** (`logVerdicts_eq`), the
  lines being the host's, in order (`readLogReq_reads_the_lines_as_sent`), and a rendering is of
  the line at its number (`logAnswer_renders_the_line_at_its_number`).
* **R10.**  `mkLogReq?` is the only constructor of a `VLogReq`: it refuses by name a `from` of 0 or
  past `2^40`, more than 32,768 lines, a `headersFrom` past `2^40`, more than 4,096 render lines
  and a render line outside the tail, and an accepted request is inside every bound
  (`LogReq.wf_bounds`).  The decoder measures `lines` before reading an element
  (`readLogReq_refuses_more_lines_than_the_bound`).  `Cal.mkTz?` is the only constructor of a
  zone; `readTz` refuses each defect by name, the bounds before `then`'s elements
  (`readTz_refuses_a_long_key`, `readTz_refuses_too_many_transitions`, `readTz_refuses_by_name`).
* **Witnesses** (each probed under `MemoryMax=8G timeout 120`; every string a parser reads is a
  `List Char` literal, AGENTS §5.10a).  The first probe of the four-line tail spelled its lines as
  escaped `String` literals under `.toList` and was **killed at the 8 GB cap** (exit 143): the
  string-literal trap of §5.10a again.  Spelled as character lists, it takes under a second. -/

section B4


theorem runPlan_ok_shape (plan : WfPlan) (cmds : List ReqCmd) (r : JVal)
    (h : runPlan plan cmds = .ok r) : ∃ kvs, r = jone "ok" (.obj kvs) := by
  unfold runPlan at h
  cases hA : applyAllR cmds plan with
  | error k => simp [hA] at h; cases h
  | ok qr =>
    obtain ⟨q, rep⟩ := qr
    simp only [hA] at h
    exact ⟨_, (Except.ok.inj h).symm⟩

theorem run_ok_shape (j : JVal) (r : JVal) (h : run j = .ok r) :
    ∃ kvs, r = jone "ok" (.obj kvs) := by
  simp only [run, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (split at h)
  all_goals first
    | (cases h; done)
    | (exact runPlan_ok_shape _ _ _ h)

theorem runWithLog_without_a_log_is_run (j : JVal) (h : readLogSection j = .ok none) :
    runWithLog j = run j := by
  simp [runWithLog, h]

theorem a_request_without_tz_or_log_is_read_as_before (j : JVal)
    (htz : jget j "tz" = .ok none) (hlog : jget j "log" = .ok none) : runWithLog j = run j := by
  apply runWithLog_without_a_log_is_run
  cases j <;> simp [readLogSection, htz, hlog]

theorem runWithLog_refuses_a_log_section_first (j e : JVal) (h : readLogSection j = .error e) :
    runWithLog j = .error e := by
  simp [runWithLog, h]

theorem runWithLog_puts_the_log_after_the_report (j v : JVal) (r : VLogReq)
    (h : readLogSection j = .ok (some r)) (hrun : run j = .ok v) :
    ∃ kvs, v = jone "ok" (.obj kvs) ∧
      runWithLog j = .ok (jone "ok" (.obj (kvs ++ [("log".toList, logAnswer r)]))) := by
  obtain ⟨kvs, rfl⟩ := run_ok_shape j v hrun
  exact ⟨kvs, rfl, by simp [runWithLog, h, hrun, withLog, jone, Except.map]⟩

theorem readStep_fold (l : List (Option (List Char))) :
    ∀ (acc : List Log.Verdict) (n : Nat),
      (l.foldl readStep (acc, n)) =
        (((l.zipIdx n).map (fun p => Log.readLine p.2 p.1)).reverse ++ acc, n + l.length) := by
  induction l with
  | nil => intro acc n; simp
  | cons seg rest ih =>
    intro acc n
    simp only [List.foldl_cons, readStep]
    rw [ih]
    simp [List.zipIdx_cons, Nat.add_assoc, Nat.add_comm 1]

theorem logVerdicts_eq (r : LogReq) :
    logVerdicts r = (r.lines.zipIdx r.from_).map (fun p => Log.readLine p.2 p.1) := by
  simp [logVerdicts, readStep_fold]


theorem mkLogReq?_ok_iff (r : LogReq) : (mkLogReq? r).toBool = r.wf := by
  unfold mkLogReq? LogReq.wf
  split <;> simp_all [Except.toBool]

theorem mkLogReq?_keeps_the_request (r : LogReq) (v : VLogReq) (h : mkLogReq? r = .ok v) :
    v.val = r := by
  unfold mkLogReq? at h
  split at h
  · cases h
  · cases h; rfl

theorem mkLogReq?_error_is_the_fault (r : LogReq) (f : LogRefusal) :
    mkLogReq? r = .error f ↔ r.fault = some f := by
  unfold mkLogReq?
  split <;> simp_all

theorem mkLogReq?_refuses_a_from_of_zero_or_past_2_40 (r : LogReq)
    (h : r.from_ = 0 ∨ logLineBound ≤ r.from_) : mkLogReq? r = .error (.badLogReq .from_) := by
  rw [mkLogReq?_error_is_the_fault]; simp [LogReq.fault, h]

theorem mkLogReq?_refuses_too_many_lines (r : LogReq) (h0 : 0 < r.from_)
    (h1 : r.from_ < logLineBound) (h : maxLogLines < r.lines.length) :
    mkLogReq? r = .error .tooManyLines := by
  rw [mkLogReq?_error_is_the_fault]
  simp [LogReq.fault, h, Nat.pos_iff_ne_zero.mp h0, Nat.not_le.mpr h1]

theorem mkLogReq?_refuses_headersFrom_past_2_40 (r : LogReq) (h0 : 0 < r.from_)
    (h1 : r.from_ < logLineBound) (h2 : r.lines.length ≤ maxLogLines) (hf : Nat)
    (hh : r.headersFrom = some hf) (hb : logLineBound ≤ hf) :
    mkLogReq? r = .error (.badLogReq .headersFrom) := by
  rw [mkLogReq?_error_is_the_fault]
  simp [LogReq.fault, Nat.pos_iff_ne_zero.mp h0, Nat.not_le.mpr h1, Nat.not_lt.mpr h2, hh, hb]

theorem mkLogReq?_refuses_too_many_render_lines (r : LogReq) (h0 : 0 < r.from_)
    (h1 : r.from_ < logLineBound) (h2 : r.lines.length ≤ maxLogLines)
    (h3 : ∀ hf, r.headersFrom = some hf → hf < logLineBound) (h : maxRenderLines < r.render.length) :
    mkLogReq? r = .error (.badLogReq .render) := by
  rw [mkLogReq?_error_is_the_fault]
  have h3' : r.headersFrom.any (fun h => decide (logLineBound ≤ h)) = false := by
    cases hh : r.headersFrom with
    | none => rfl
    | some x => simp [Nat.not_le.mpr (h3 x hh)]
  simp [LogReq.fault, Nat.pos_iff_ne_zero.mp h0, Nat.not_le.mpr h1, Nat.not_lt.mpr h2, h3', h]

/-- Every accepted request is inside every bound. -/
theorem LogReq.wf_bounds (r : LogReq) (h : r.wf = true) :
    0 < r.from_ ∧ r.from_ < logLineBound ∧ r.lines.length ≤ maxLogLines ∧
      (∀ hf, r.headersFrom = some hf → hf < logLineBound) ∧ r.render.length ≤ maxRenderLines ∧
      ∀ n ∈ r.render, r.from_ ≤ n ∧ n < r.from_ + r.lines.length := by
  unfold LogReq.wf LogReq.fault at h
  split at h
  · simp at h
  rename_i ha
  split at h
  · simp at h
  rename_i hb
  split at h
  · simp at h
  rename_i hc
  split at h
  · simp at h
  rename_i hd
  split at h
  · simp at h
  rename_i he
  refine ⟨by omega, by omega, by omega, ?_, by omega, ?_⟩
  · intro hf hh; simp [hh] at hc; omega
  · intro n hn
    have := List.find?_eq_none.mp he n hn
    simp at this; omega

theorem mkLogReq?_refuses_a_render_line_outside_the_tail (r : LogReq) (h0 : 0 < r.from_)
    (h1 : r.from_ < logLineBound) (h2 : r.lines.length ≤ maxLogLines)
    (h3 : ∀ hf, r.headersFrom = some hf → hf < logLineBound) (h4 : r.render.length ≤ maxRenderLines)
    (n : Nat) (hn : n ∈ r.render) (hout : n < r.from_ ∨ r.from_ + r.lines.length ≤ n) :
    ∃ m, mkLogReq? r = .error (.renderNotInTail m) ∧ (m < r.from_ ∨ r.from_ + r.lines.length ≤ m) := by
  have hwf : r.wf = false := by
    cases hw : r.wf
    · rfl
    · have := (LogReq.wf_bounds r hw).2.2.2.2.2 n hn; omega
  have h3' : r.headersFrom.any (fun h => decide (logLineBound ≤ h)) = false := by
    cases hh : r.headersFrom with
    | none => rfl
    | some x => simp [Nat.not_le.mpr (h3 x hh)]
  cases hf : r.render.find? (fun n => n < r.from_ || r.from_ + r.lines.length ≤ n) with
  | none =>
    have := List.find?_eq_none.mp hf n hn
    simp at this; omega
  | some m =>
    refine ⟨m, ?_, ?_⟩
    · rw [mkLogReq?_error_is_the_fault]
      simp [LogReq.fault, Nat.pos_iff_ne_zero.mp h0, Nat.not_le.mpr h1, Nat.not_lt.mpr h2, h3',
        Nat.not_lt.mpr h4, hf]
    · have := List.find?_some hf
      simpa using this


theorem readTz_refuses_a_long_key (kvs : List (List Char × JVal)) (key b : List Char)
    (xs : List JVal) (base : Cal.VOffset)
    (hk : jget (.obj kvs) "key" = .ok (some (.str key)))
    (hb : jget (.obj kvs) "base" = .ok (some (.str b))) (hbo : readTzOffset b = some base)
    (ht : jget (.obj kvs) "then" = .ok (some (.arr xs))) (hl : 128 < key.length) :
    readTz (.obj kvs) = .error .keyTooLong := by
  simp [readTz, hk, hb, hbo, ht, hl]

theorem readTz_refuses_too_many_transitions (kvs : List (List Char × JVal)) (key b : List Char)
    (xs : List JVal) (base : Cal.VOffset)
    (hk : jget (.obj kvs) "key" = .ok (some (.str key)))
    (hb : jget (.obj kvs) "base" = .ok (some (.str b))) (hbo : readTzOffset b = some base)
    (ht : jget (.obj kvs) "then" = .ok (some (.arr xs))) (hkl : key.length ≤ 128)
    (hl : 4096 < xs.length) :
    readTz (.obj kvs) = .error .tooManyTransitions := by
  simp [readTz, hk, hb, hbo, ht, hl, Nat.not_lt.mpr hkl]

theorem readLogReq_refuses_more_lines_than_the_bound (kvs : List (List Char × JVal)) (n : Nat)
    (xs : List JVal) (hc : nullOrAbsent (.obj kvs) "ckpt" = true)
    (hf : jget (.obj kvs) "from" = .ok (some (.num n)))
    (hl : jget (.obj kvs) "lines" = .ok (some (.arr xs))) (hn : maxLogLines < xs.length) :
    readLogReq (.obj kvs) = .error .tooManyLines := by
  simp [readLogReq, hc, hf, hl, hn]

/-- A line as the host sent it: a string, or `null` for a line that is not UTF-8. -/
def segOf : JVal → Option (List Char)
  | .str s => some s
  | _ => none

theorem lineStep_error (xs : List JVal) (e : LogRefusal) :
    xs.foldl lineStep (.error e) = .error e := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp only [List.foldl_cons, lineStep]; exact ih

theorem lineStep_fold (xs : List JVal) : ∀ (acc ys : List (Option (List Char))),
    xs.foldl lineStep (.ok acc) = .ok ys → ys = (xs.map segOf).reverse ++ acc := by
  induction xs with
  | nil => intro acc ys h; simp at h; simp [h]
  | cons x rest ih =>
    intro acc ys h
    simp only [List.foldl_cons] at h
    cases x with
    | str s => have := ih _ _ h; simp [this, segOf]
    | null => have := ih _ _ h; simp [this, segOf]
    | _ => simp only [lineStep] at h; rw [lineStep_error] at h; cases h

/-- **The op reads the lines the host sent, in order** (with `logVerdicts_eq`: line `from + k` is
`Log.readLine` of the `k`-th element). -/
theorem readLogReq_reads_the_lines_as_sent (j : JVal) (v : VLogReq) (h : readLogReq j = .ok v) :
    ∃ xs, jget j "lines" = .ok (some (.arr xs)) ∧ v.val.lines = xs.map segOf := by
  unfold readLogReq at h
  repeat' (split at h)
  all_goals first
    | (cases h; done)
    | skip
  rename_i xs hl _ _ rev hfold _ _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨xs, hl, ?_⟩
  rw [mkLogReq?_keeps_the_request _ _ h, lineStep_fold xs [] rev hfold]
  simp

theorem LogReq.wf_render_in_tail (r : LogReq) (h : r.wf = true) (n : Nat) (hn : n ∈ r.render) :
    r.from_ ≤ n ∧ n < r.from_ + r.lines.length := by
  unfold LogReq.wf LogReq.fault at h
  split at h; · simp at h
  split at h; · simp at h
  split at h; · simp at h
  split at h; · simp at h
  split at h; · simp at h
  rename_i he
  have := List.find?_eq_none.mp he n hn
  simp at this; omega

/-- **A rendering is of the line the host sent at that number**: for each `want.render` line `n`
of an accepted request, the element `n − from` of `lines` is there, and the verdict the answer
renders is `Log.readLine n` of it. -/
theorem logAnswer_renders_the_line_at_its_number (r : VLogReq) (n : Nat) (hn : n ∈ r.val.render) :
    ∃ seg, r.val.lines[n - r.val.from_]? = some seg ∧
      (logVerdicts r.val).toArray[n - r.val.from_]? = some (Log.readLine n seg) := by
  obtain ⟨h1, h2⟩ := LogReq.wf_render_in_tail r.val r.property n hn
  have hlt : n - r.val.from_ < r.val.lines.length := by omega
  refine ⟨r.val.lines[n - r.val.from_], by simp [hlt], ?_⟩
  rw [List.getElem?_toArray, logVerdicts_eq, List.getElem?_map, List.getElem?_zipIdx]
  simp [hlt, Nat.add_sub_cancel' h1]


/-! ### Witnesses -/

/-- `±HH:MM:SS`, read: west, east, seconds; `-00:00:00`, `+24:00:00`, a minute of 60, no seconds and
a trailing sign refused. -/
theorem readTzOffset_reads_the_table_spelling :
    (readTzOffset ['-', '0', '6', ':', '0', '0', ':', '0', '0']).map Subtype.val = some ⟨true, 21600⟩ ∧
    (readTzOffset ['+', '0', '5', ':', '4', '5', ':', '0', '0']).map Subtype.val = some ⟨false, 20700⟩ ∧
    (readTzOffset ['-', '0', '0', ':', '4', '4', ':', '3', '0']).map Subtype.val = some ⟨true, 2670⟩ ∧
    (readTzOffset ['+', '0', '0', ':', '0', '0', ':', '0', '0']).map Subtype.val = some ⟨false, 0⟩ ∧
    readTzOffset ['-', '0', '0', ':', '0', '0', ':', '0', '0'] = none ∧
    readTzOffset ['+', '2', '4', ':', '0', '0', ':', '0', '0'] = none ∧
    readTzOffset ['+', '0', '5', ':', '6', '0', ':', '0', '0'] = none ∧
    readTzOffset ['+', '0', '5', ':', '3', '0'] = none ∧
    readTzOffset ['0', '5', ':', '3', '0', ':', '0', '0', '+'] = none :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- A transition instant is a stamp at UTC in whole seconds: 2026-03-08T08:00:00Z is Chicago's
spring transition (`Cal.chicago2026`); the same instant written at −06:00, and a half second,
are refused. -/
theorem readTzInstant_reads_utc_whole_seconds :
    readTzInstant ['2', '0', '2', '6', '-', '0', '3', '-', '0', '8', 'T', '0', '8', ':', '0', '0', ':', '0', '0', 'Z'] = some ⟨63908553600, 0⟩ ∧
    readTzInstant ['2', '0', '2', '6', '-', '0', '3', '-', '0', '8', 'T', '0', '2', ':', '0', '0', ':', '0', '0', '-', '0', '6', ':', '0', '0'] = none ∧
    readTzInstant ['2', '0', '2', '6', '-', '0', '3', '-', '0', '8', 'T', '0', '8', ':', '0', '0', ':', '0', '0', '.', '5', 'Z'] = none :=
  ⟨by decide, by decide, by decide⟩

/-- A read table as a plain value, for decided witnesses (`Except` has no `DecidableEq`). -/
def tzRead : Except TzWhy Cal.Tz → Sum TzWhy Cal.TzTable
  | .ok z => .inr z.val
  | .error w => .inl w

/-- A `tz` section of Chicago's key, `base` and transitions `trans`. -/
def tzWith (base : List Char) (trans : List (List Char × List Char)) : JVal :=
  .obj [("key".toList, .str "America/Chicago".toList), ("base".toList, .str base),
    ("then".toList, .arr (trans.map fun p => .arr [.str p.1, .str p.2]))]

/-- **The witness table reads as `Cal.chicago2026`**, B1's two-transition Chicago table. -/
theorem readTz_reads_the_witness_table :
    tzRead (readTz (tzWith ['-', '0', '6', ':', '0', '0', ':', '0', '0'] [(['2', '0', '2', '6', '-', '0', '3', '-', '0', '8', 'T', '0', '8', ':', '0', '0', ':', '0', '0', 'Z'], ['-', '0', '5', ':', '0', '0', ':', '0', '0']), (['2', '0', '2', '6', '-', '1', '1', '-', '0', '1', 'T', '0', '7', ':', '0', '0', ':', '0', '0', 'Z'], ['-', '0', '6', ':', '0', '0', ':', '0', '0'])])) = .inr Cal.chicago2026 := by
  decide

/-- **Each defect by name**: two transitions out of order, two at one instant, an instant written
at −06:00, an offset without its hour's zero, `-00:00:00` as the base, a transition that is not a
pair, a key that is not a string, a section that is not an object. -/
theorem readTz_refuses_by_name :
    tzRead (readTz (tzWith ['-', '0', '6', ':', '0', '0', ':', '0', '0'] [(['2', '0', '2', '6', '-', '1', '1', '-', '0', '1', 'T', '0', '7', ':', '0', '0', ':', '0', '0', 'Z'], ['-', '0', '6', ':', '0', '0', ':', '0', '0']), (['2', '0', '2', '6', '-', '0', '3', '-', '0', '8', 'T', '0', '8', ':', '0', '0', ':', '0', '0', 'Z'], ['-', '0', '5', ':', '0', '0', ':', '0', '0'])])) = .inl .unsorted ∧
    tzRead (readTz (tzWith ['-', '0', '6', ':', '0', '0', ':', '0', '0'] [(['2', '0', '2', '6', '-', '0', '3', '-', '0', '8', 'T', '0', '8', ':', '0', '0', ':', '0', '0', 'Z'], ['-', '0', '5', ':', '0', '0', ':', '0', '0']), (['2', '0', '2', '6', '-', '0', '3', '-', '0', '8', 'T', '0', '8', ':', '0', '0', ':', '0', '0', 'Z'], ['-', '0', '6', ':', '0', '0', ':', '0', '0'])])) = .inl .unsorted ∧
    tzRead (readTz (tzWith ['-', '0', '6', ':', '0', '0', ':', '0', '0'] [(['2', '0', '2', '6', '-', '0', '3', '-', '0', '8', 'T', '0', '2', ':', '0', '0', ':', '0', '0', '-', '0', '6', ':', '0', '0'], ['-', '0', '5', ':', '0', '0', ':', '0', '0'])])) = .inl .instant ∧
    tzRead (readTz (tzWith ['-', '0', '6', ':', '0', '0', ':', '0', '0'] [(['2', '0', '2', '6', '-', '0', '3', '-', '0', '8', 'T', '0', '8', ':', '0', '0', ':', '0', '0', 'Z'], ['-', '5', ':', '0', '0', ':', '0', '0'])])) = .inl .offset ∧
    tzRead (readTz (tzWith ['-', '0', '0', ':', '0', '0', ':', '0', '0'] [])) = .inl .base ∧
    tzRead (readTz (.obj [("key".toList, .str ['k']), ("base".toList, .str ['+', '0', '0', ':', '0', '0', ':', '0', '0']),
        ("then".toList, .arr [.str ['x']])])) = .inl .transition ∧
    tzRead (readTz (.obj [("key".toList, .num 1)])) = .inl .key ∧
    tzRead (readTz (.arr [])) = .inl .shape :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- A response as a plain value, for decided witnesses. -/
def answered : Except JVal JVal → Sum JVal JVal
  | .ok v => .inr v
  | .error e => .inl e

/-- The zone of the end-to-end witnesses: UTC, no transitions. -/
def utcTzJson : JVal :=
  .obj [("key".toList, .str ['U', 'T', 'C']), ("base".toList, .str ['+', '0', '0', ':', '0', '0', ':', '0', '0']), ("then".toList, .arr [])]

/-- A `drop` line of 50 characters, spelled as characters (the parser reads it). -/
def logWitnessLine : List Char :=
  ['{', '"', 't', '"', ':', '"', '2', '0', '2', '6', '-', '0', '9', '-', '0', '7', 'T', '0', '9', ':', '0', '0', ':', '0', '0', 'Z', '"', ',', '"', 'e', 'v', '"', ':', '"', 'd', 'r', 'o', 'p', '"', ',', '"', 'i', 'd', '"', ':', '"', 'a', '1', '"', '}']

def logWitnessRequest : JVal :=
  .obj [("docs".toList, .arr []), ("tz".toList, utcTzJson),
    ("log".toList, .obj [("ckpt".toList, .null), ("from".toList, .num 7),
      ("lines".toList, .arr [.str logWitnessLine, .str [], .null, .str ['{', '"', 'e', 'v', '"', ':', '7', '}']]),
      ("terminated".toList, .bool true),
      ("want".toList, .obj [("headersFrom".toList, .num 7), ("render".toList, .arr [.num 7, .num 8])])])]

def logWitnessAnswer : JVal :=
  .obj [("lines".toList, .num 10),
    ("warnings".toList, .arr [.obj [("line".toList, .num 9), ("w".toList, .str "invalidUtf8".toList)],
                              .obj [("line".toList, .num 10), ("w".toList, .str "noT".toList)]]),
    ("facts".toList, .null),
    ("headers".toList, .arr [.arr [.num 7, .str "drop".toList, .str "a1".toList]]),
    ("render".toList, .arr [.arr [.num 7, .str "{\"t\":\"2026-09-07T09:00:00+00:00\",\"ev\":\"drop\",\"id\":\"a1\"}".toList,
                                  .str "2026-09-07 09:00".toList],
                            .arr [.num 8, .null, .null]])]

set_option maxRecDepth 8000 in
/-- **The op end to end, on a tail of four lines from line 7**: a `drop` (a header with its id, and
a rendering in serde's bytes with `+00:00` for UTC and the `tm log` column), a blank line, a line
that is not UTF-8, and `{"ev":7}` (no `t`).  The `ok` object is `run`'s, with `log` after
`report`. -/
theorem the_log_op_reads_a_four_line_tail :
    answered (runWithLog logWitnessRequest)
      = .inr (jone "ok" (.obj [("docs".toList, .arr []), ("report".toList, reportJson Report.empty),
          ("log".toList, logWitnessAnswer)])) := by
  decide

set_option maxRecDepth 8000 in
/-- **The section's refusals reach the response by name**: `log` without `tz`; a checkpoint at B4;
a render line past the tail; a malformed `tz` without `log`; a `tz` that is not an object. -/
theorem the_log_section_refuses_by_name :
    answered (runWithLog (.obj [("docs".toList, .arr []), ("log".toList, .obj [])]))
      = .inl LogRefusal.tzAbsent.json ∧
    answered (runWithLog (.obj [("docs".toList, .arr []), ("tz".toList, utcTzJson),
        ("log".toList, .obj [("ckpt".toList, .obj [])])]))
      = .inl (LogRefusal.badLogReq .ckpt).json ∧
    answered (runWithLog (.obj [("docs".toList, .arr []), ("tz".toList, utcTzJson),
        ("log".toList, .obj [("from".toList, .num 1), ("lines".toList, .arr [.null]),
          ("terminated".toList, .bool false), ("want".toList, .obj [("render".toList, .arr [.num 2])])])]))
      = .inl (LogRefusal.renderNotInTail 2).json ∧
    answered (runWithLog (.obj [("docs".toList, .arr []), ("tz".toList, tzWith ['+', '2', '4', ':', '0', '0', ':', '0', '0'] [])]))
      = .inl (LogRefusal.badTz .base).json ∧
    answered (runWithLog (.obj [("docs".toList, .arr []), ("tz".toList, .num 3)]))
      = .inl (LogRefusal.badTz .shape).json :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

end B4

/-! ## Stage 5 D10 L5: a loaded calendar's wall reaches the lookahead

APPENDED 2026-09-14 (stage-5 D10 track, step L5; design §13.4).  The loaded-plan witness: a
one-line calendar holding the §4.3 meeting on Wednesday 2026-09-09 loads, `wallIndex` reads it
once as one wall on that date (fork `Ctx::walls_on`), and through it Wednesday's window ends at
16:00 and the twin's Wednesday is the fork's `[0, 0, 0, 0, 180, 180]` times `capDen`
(`Look.a_wednesday_wall_moves_the_window_and_keeps_the_budget`).  The plan is evaluated under
`decide` once, in `the_look_wall_calendar_indexes_one_wednesday_wall`, and the capacity
statement is reached by rewriting with that equation, so no `decide` holds both the load and
the lookahead.  This module imports `Lookahead` for it (it imported `Capacity` already). -/

/-- A one-line calendar: fork fixture `calendar/2026-W37.md`'s meeting, moved to Wednesday. -/
def lookWallWitness : List ReqDoc :=
  [⟨"calendar/2026-W37.md", none,
     ["- [ ] 3 Meeting w/ host      at:2026-09-09T12:50/13:50 loc:zoom ^g1".toList]⟩]

set_option maxRecDepth 40000 in
/-- **The calendar witness loads.** -/
theorem the_look_wall_witness_loads : loadsOk lookWallWitness = true := by decide

/-- The loaded calendar.  Total by `the_look_wall_witness_loads`: the error branch is refuted,
not defaulted. -/
def lookWallPlan : WfPlan :=
  match h : loadPlan lookWallWitness with
  | .ok p => p
  | .error _ => absurd the_look_wall_witness_loads (by simp [loadsOk, h])

set_option maxRecDepth 40000 in
/-- **`wallIndex` reads the loaded calendar once: one wall, on Wednesday, 12:50 to 13:50 in
Chicago** (an open `[ ]` item with an `at:` interval and no `buffer:`). -/
theorem the_look_wall_calendar_indexes_one_wednesday_wall :
    Look.wallIndex Cal.chicago 60 lookWallPlan.val = Look.wednesdayWall := by
  decide

/-- **A Wednesday wall on a loaded plan gives Wednesday's window end 16:00, and the twin's
capacity is the fork's value written out by hand** (design §13.4): the lounge day at `p = 0.9`
keeps 180 minutes at level 5 and 180 at level 4, times `capDen`. -/
theorem a_loaded_wednesday_wall_moves_the_window_and_keeps_the_budget :
    (Look.windowOn Cal.chicago 739867 420 1140 480
        (Look.wallsOn (Look.wallIndex Cal.chicago 60 lookWallPlan.val) 739867)).2
      = (Cal.instantOf Cal.chicago 739867 960).sec ∧
    ((Look.lookahead { Look.specInput with walls := Look.wallIndex Cal.chicago 60 lookWallPlan.val }.twin)[2]?).map
        (fun c => (c.day, (List.finRange 6).map c.numAt))
      = some (739867, [0, 0, 0, 0, 180 * Look.capDen, 180 * Look.capDen]) := by
  rw [the_look_wall_calendar_indexes_one_wednesday_wall]
  exact ⟨Look.a_wednesday_wall_moves_the_window_and_keeps_the_budget.2.1,
    Look.a_wednesday_wall_moves_the_window_and_keeps_the_budget.2.2.2⟩

/-! ## Stage 5 D10 L6: capacity on the wire — every bound named, units as digit strings, gap 77 closed

APPENDED 2026-09-14 (stage-5 D10 track, step L6; design §13.6, §10.1–§10.4).  A request may carry
a `capacity` section and the zone table `tz`.  The kernel reads both with the smart constructors
of `Lookahead.lean` (L5's `mkInput?`, L1's `mkWeight?`, L6's `mkDayCfg?`, `mkStep?`, `curveOk`,
`priorOk`, `energyOk`, `homeMaxOk`), B1's `Cal.mkTz?`, and step 2's priority decoders
(`binsOfPairs?`, `safetyOf?`, `defaultPrioOf?`: **gap 77 is closed**, since the wire now calls
them), runs L5's `lookahead` over the loaded plan's walls, and answers the request as `run` does
with one more key, `lookahead`, after `report`.  A request without `capacity` is answered exactly
as before (`runCap_without_capacity_is_run`, `callExport_without_capacity_is_call`).

```jsonc
// request (added keys)
"tz": {"key": "America/Chicago|2025b|1900-2200", "base": "-06:00:00",
       "then": [["2026-03-08T08:00:00Z", "-05:00:00"], …]},          // ≤ 4,096, strictly increasing
"capacity": {
  "pLounge":  {"model": {"Mon": {"num": "9", "den": "10"}}, "config": {"Mon": {…}, … all 7}},   // digit strings
  "arrival":  {"model": {"Mon": "07:10"}, "config": {"Mon": "07:00", … all 7}},
  "wake":     null | {"sec": 21940, "ns": 250000000},              // today's logged wake, a time of day
  "energy":   {"lounge": [12 entries < 256], "home": […]},          // either may be absent
  "prior":    {"lounge": [{"from": {"num": 0, "den": 1}, "to": {"num": 1, "den": 1}, "level": 4}, …], …},
  "homeMaxCi": 3,
  "day":      {"breakMin": 20, "breakAfterBlocks": 2, "minLastBlockMin": 30,
               "windowHours": {"num": 8, "den": 1}, "windowCap": "19:00", "budgetRatio": {"num": 75, "den": 100}},
  "priority": {"bins": [{"num": 5, "den": 10}, …], "safety": {"num": 13, "den": 10}, "defaultPriority": 3},
  "days": 7,
  "day0": [0, 0, 60, 120, 60, 0]}                                   // until L9
// the request's `now` is today and its `blockMin` is `[day] block_min`: both required with `capacity`
// response: the `ok` object gains, after `report`,
"lookahead": {"den": "1000000000000000000",
              "days": [{"day": "2026-09-07", "numAt": ["0", "0", "0", "60000000000000000000", …]}, …]}   // first min(days, 7)
// refusal
{"err": {"capacity": "<name> <key>"}}
```

**Unit counts are digit strings** (D17): one minute is `10^18` units, past `2^53` and `u64`, so no
unit count is a JSON number, and `readNat (digitsOf n) = some n` is the host's reading
(`unitsJson_reads_back`).  **The weight is a pair of digit strings**, refused by name above 18
decimal places (`weightPrecision`), above one (`weightAboveOne`) or malformed (`badWeight`).  Every
pair sent is checked, the model's and the config's (§13.2: the host names the file, the kernel is
the authority), and the kernel then picks the model's, else the config's (D10-4).

**Refusal order.**  `nowAbsent`, `blockMinAbsent`, then the zone (`tzAbsent`, `badTz <why>`), then the
section in the order of the example (a key that is absent, carried twice or of the wrong JSON type is
refused before any bound of its own object), then L5's `mkInput?` (`lookaheadTooLong` first), then a
lookahead that would run past year 9999 (`lookaheadTooLong`, so every emitted date renders as one).
The documents load before the section is read, and the section is read before the commands run.

**What is not on the wire yet, by name.**  The response carries no `grants`: which candidates enter
the EDF pass is gap 80's, and step 3's pass is gap 106's (both L8, with the priority wiring).  The
decoded `priority` ladder, safety and default are held in `CapReq` for that wiring and read by no
response key.  `tz` is read here because the lookahead needs it; the D9 track's B4 owns the `tz` key
for the `log` op, and the merge keeps one reader.

**Stage 5 D10 L8 (kernel half) extends this section** (gaps 80, 106, 107, 109 and 110 closed): an
optional `capacity.candidates` object (`readCands`, at most 1,024 records), and `lookahead.grants`,
one per candidate in request order (`grantJson` over `Look.priorities`, which uses the ladder, the
safety and the default); the zone is read once (`zoneOf`, feeding `logSectionWith` and
`readCapacityZ`); and a capacity request that also carries commands is refused by name,
`capacityWithCommands`, because the walls are the documents as sent.

**Stage 5 D10 L8 (host half) adds the floor pass** (gap 79 closed): a candidate record may carry
`"floor": {"left": 120, "until": "2026-09-30"}` (`readFloor`), and a candidate that does not enter the
pass, is not a wall and has a floor is answered at it (`grantJsonF` over `Look.prioritiesWithFloors`,
class `floor`).  A request without floors is answered as before (`grantJsonF_without_a_floor`,
`Look.prioritiesWithFloors_without_floors`).
-/

namespace CapWire

open Look

/-! ### Names -/

/-- A weekday's key in the `pLounge` and `arrival` tables (fork `WeekdayMap`'s serde keys). -/
def wdKey : Cal.Weekday → String
  | .monday => "Mon" | .tuesday => "Tue" | .wednesday => "Wed" | .thursday => "Thu"
  | .friday => "Fri" | .saturday => "Sat" | .sunday => "Sun"

/-- Which reading of a weekday table (D10-4: the host sends both, the kernel picks). -/
inductive Src where
  | model
  | config
deriving DecidableEq, Repr

/-- A structural key of the section: absent where it is required, carried twice, or not the JSON
type it must be. -/
inductive Part where
  | capacity
  | pLounge
  | pLoungeModel
  | pLoungeConfig
  | arrival
  | arrivalModel
  | arrivalConfig
  | energy
  | prior
  | day
  | priority
  | days
  /-- Stage 5 D10 L8: the `candidates` object, its `hysteresis` and its `items`. -/
  | candidates
deriving DecidableEq, Repr

/-- Stage 5 D10 L8: a key of one candidate record (`badCandidate <position> <key>`). -/
inductive CandKey where
  | id
  | ci
  | rootPrio
  | remaining
  | due
  | window
  | wall
  | optional
  | overdue
  | mandatory
  | hot
  | yesterday
  /-- Stage 5 D10 L8 host half: the record's `floor` object (gap 79). -/
  | floor
deriving DecidableEq, Repr

-- `CapWire.TzWhy` (`shape key base trans table`) was removed at the merge of the D9 track's B4
-- (gap 108 closed): `badTz` carries B4's `Tm.TzWhy`, the one zone reader's names.

/-- **A capacity refusal, by name** (AGENTS §5.7; design §13.6's table). -/
inductive Refusal where
  | nowAbsent
  | blockMinAbsent
  | tzAbsent
  | badTz (why : TzWhy)
  | badCapacity (p : Part)
  | weight (e : WErr) (src : Src) (wd : Cal.Weekday)
  | badClock (src : Src) (wd : Cal.Weekday)
  | badWindowCap
  | badWake
  | badCurve (loc : Loc)
  | badPrior (key : List Char)
  | step (e : StepErr) (key : List Char)
  | badCap
  | badDay (k : DayKey)
  | lookaheadTooLong
  | badDay0
  | badBins
  | badSafety
  | badDefaultPriority
  /-- Stage 5 D10 L8: more than 1,024 candidates (R10). -/
  | tooManyCandidates
  /-- Stage 5 D10 L8: a candidate record's key, by the record's position and the key's name. -/
  | badCandidate (i : Nat) (k : CandKey)
  /-- Stage 5 D10 L8, gap 109: a capacity request that also carries commands. -/
  | capacityWithCommands
deriving DecidableEq, Repr

def Src.name : Src → String
  | .model => "model" | .config => "config"

def Part.name : Part → String
  | .capacity => "capacity" | .pLounge => "pLounge" | .pLoungeModel => "pLounge.model"
  | .pLoungeConfig => "pLounge.config" | .arrival => "arrival" | .arrivalModel => "arrival.model"
  | .arrivalConfig => "arrival.config" | .energy => "energy" | .prior => "prior" | .day => "day"
  | .priority => "priority" | .days => "days" | .candidates => "candidates"

def CandKey.name : CandKey → String
  | .id => "id" | .ci => "ci" | .rootPrio => "rootPrio" | .remaining => "remaining" | .due => "due"
  | .window => "window" | .wall => "wall" | .optional => "optional" | .overdue => "overdue"
  | .mandatory => "mandatory" | .hot => "hot" | .yesterday => "yesterday" | .floor => "floor"

def werrName : WErr → String
  | .badWeight => "badWeight" | .weightAboveOne => "weightAboveOne" | .weightPrecision => "weightPrecision"

def stepErrName : StepErr → String
  | .badStep => "badStep" | .badLevel => "badLevel"

def dayKeyName : DayKey → String
  | .blockMin => "blockMin" | .breakMin => "breakMin" | .breakAfterBlocks => "breakAfterBlocks"
  | .minLastBlockMin => "minLastBlockMin" | .windowHours => "windowHours" | .budgetRatio => "budgetRatio"

def locName : Loc → String
  | .lounge => "lounge" | .home => "home"

/-- The refusal's text: its name, then the key it names. -/
def Refusal.text : Refusal → String
  | .nowAbsent => "nowAbsent"
  | .blockMinAbsent => "blockMinAbsent"
  | .tzAbsent => "tzAbsent"
  | .badTz w => "badTz " ++ w.name
  | .badCapacity p => "badCapacity " ++ p.name
  | .weight e s wd => werrName e ++ " pLounge." ++ s.name ++ "." ++ wdKey wd
  | .badClock s wd => "badClock arrival." ++ s.name ++ "." ++ wdKey wd
  | .badWindowCap => "badClock day.windowCap"
  | .badWake => "badWake"
  | .badCurve l => "badCurve energy." ++ locName l
  | .badPrior k => "badPrior prior." ++ String.ofList k
  | .step e k => stepErrName e ++ " prior." ++ String.ofList k
  | .badCap => "badCap homeMaxCi"
  | .badDay k => "badDay " ++ dayKeyName k
  | .lookaheadTooLong => "lookaheadTooLong"
  | .badDay0 => "badDay0"
  | .badBins => "badBins"
  | .badSafety => "badSafety"
  | .badDefaultPriority => "badDefaultPriority"
  | .tooManyCandidates => "tooManyCandidates"
  | .badCandidate i k => "badCandidate " ++ String.ofList (digitsOf i) ++ " " ++ k.name
  | .capacityWithCommands => "capacityWithCommands"

/-- The refusal on the wire: `{"err": {"capacity": "<name> <key>"}}`. -/
def refusalJson (r : Refusal) : JVal := jone "err" (jone "capacity" (.str r.text.toList))

/-! ### Readers: every value through its smart constructor -/

/-- A required key: absent, `null`, carried twice, or read off a non-object is `r`. -/
def need (j : JVal) (k : String) (r : Refusal) : Except Refusal JVal :=
  match jget j k with
  | .ok (some .null) => .error r
  | .ok (some v) => .ok v
  | _ => .error r

/-- An optional key: absent or `null` is `none`; carried twice or read off a non-object is `r`. -/
def opt (j : JVal) (k : String) (r : Refusal) : Except Refusal (Option JVal) :=
  match jget j k with
  | .ok none => .ok none
  | .ok (some .null) => .ok none
  | .ok (some v) => .ok (some v)
  | .error _ => .error r

/-- A JSON natural. -/
def natOf : JVal → Option Nat
  | .num n => some n
  | _ => none

/-- The longest digit string a pair part may be. -/
def maxDigits : Nat := 40

/-- A digit string (D17): at least one digit, only digits, at most 40. -/
def natOfDigits : JVal → Option Nat
  | .str s => if s.length ≤ maxDigits then readNat s else none
  | _ => none

/-- `{"num": …, "den": …}`, each part read by `rd`. -/
def pairWith (rd : JVal → Option Nat) (v : JVal) : Option (Nat × Nat) :=
  match jget v "num", jget v "den" with
  | .ok (some n), .ok (some d) => (rd n).bind fun n => (rd d).map fun d => (n, d)
  | _, _ => none

/-- An `HH:MM` clock, by the clock grammar every clock field uses (`Field.parseClock`). -/
def clockOf : JVal → Option Field.Clock
  | .str s => Field.parseClock s
  | _ => none

/-- An option, or the refusal. -/
def orErr {α : Type} (o : Option α) (r : Refusal) : Except Refusal α :=
  match o with
  | some a => .ok a
  | none => .error r

/-- A natural at `k`, or `r`. -/
def natAt (v : JVal) (k : String) (r : Refusal) : Except Refusal Nat :=
  match need v k r with
  | .ok (.num n) => .ok n
  | _ => .error r

/-- A string at `k`, or `r`. -/
def strAt (v : JVal) (k : String) (r : Refusal) : Except Refusal (List Char) :=
  match need v k r with
  | .ok (.str s) => .ok s
  | _ => .error r

/-- An array at `k`, or `r`. -/
def arrAt (v : JVal) (k : String) (r : Refusal) : Except Refusal (List JVal) :=
  match need v k r with
  | .ok (.arr xs) => .ok xs
  | _ => .error r

/-- A pair of JSON naturals at `k`, or `r`. -/
def pairAt (v : JVal) (k : String) (r : Refusal) : Except Refusal (Nat × Nat) :=
  match need v k r with
  | .ok p => orErr (pairWith natOf p) r
  | .error e => .error e

/-- A clock at `k`, or `r`. -/
def clockAt (v : JVal) (k : String) (r : Refusal) : Except Refusal Field.Clock :=
  match need v k r with
  | .ok c => orErr (clockOf c) r
  | .error e => .error e

/-- **One lounge weight** (L1's `mkWeight?`): a pair of digit strings, then the constructor's names. -/
def readWeight (src : Src) (wd : Cal.Weekday) (v : JVal) : Except Refusal (Nat × Nat) :=
  match pairWith natOfDigits v with
  | none => .error (.weight .badWeight src wd)
  | some (n, d) =>
    match mkWeight? n d with
    | .ok _ => .ok (n, d)
    | .error e => .error (.weight e src wd)

/-- One arrival clock. -/
def readArrival (src : Src) (wd : Cal.Weekday) (v : JVal) : Except Refusal Field.Clock :=
  match clockOf v with
  | some c => .ok c
  | none => .error (.badClock src wd)

/-- The seven entries of a table, Monday first, as a function. -/
def ofSeven {α : Type} (mo tu we th fr sa su : α) : Cal.Weekday → α
  | .monday => mo | .tuesday => tu | .wednesday => we | .thursday => th
  | .friday => fr | .saturday => sa | .sunday => su

/-- **The model's reading of a weekday table**: an absent weekday is `none`. -/
def readWeekOpt {α : Type} (tbl : JVal) (bad : Cal.Weekday → Refusal)
    (rd : Cal.Weekday → JVal → Except Refusal α) : Except Refusal (Cal.Weekday → Option α) := do
  let one := fun (wd : Cal.Weekday) =>
    match opt tbl (wdKey wd) (bad wd) with
    | .error e => (Except.error e : Except Refusal (Option α))
    | .ok none => .ok none
    | .ok (some v) => (rd wd v).map some
  return ofSeven (← one .monday) (← one .tuesday) (← one .wednesday) (← one .thursday)
    (← one .friday) (← one .saturday) (← one .sunday)

/-- **The config's reading of a weekday table**: every weekday is required. -/
def readWeekAll {α : Type} (tbl : JVal) (bad : Cal.Weekday → Refusal)
    (rd : Cal.Weekday → JVal → Except Refusal α) : Except Refusal (Cal.Weekday → α) := do
  let one := fun (wd : Cal.Weekday) =>
    match need tbl (wdKey wd) (bad wd) with
    | .error e => (Except.error e : Except Refusal α)
    | .ok v => rd wd v
  return ofSeven (← one .monday) (← one .tuesday) (← one .wednesday) (← one .thursday)
    (← one .friday) (← one .saturday) (← one .sunday)

/-- An object, or the structural refusal. -/
def needObj (v : JVal) (p : Part) : Except Refusal JVal :=
  match v with
  | .obj _ => .ok v
  | _ => .error (.badCapacity p)

/-- **Both readings of a weekday table** (`pLounge`, `arrival`): the model's may be absent. -/
def readModelTable {α : Type} (t : JVal) (pm : Part) (bad : Cal.Weekday → Refusal)
    (rd : Cal.Weekday → JVal → Except Refusal α) : Except Refusal (Cal.Weekday → Option α) :=
  match opt t "model" (.badCapacity pm) with
  | .error e => .error e
  | .ok none => .ok (fun _ => none)
  | .ok (some mt) => (needObj mt pm).bind (fun mt => readWeekOpt mt bad rd)

def readTables {α : Type} (sec : JVal) (k : String) (p pm pc : Part)
    (bad : Src → Cal.Weekday → Refusal) (rd : Src → Cal.Weekday → JVal → Except Refusal α) :
    Except Refusal ((Cal.Weekday → Option α) × (Cal.Weekday → α)) := do
  let t0 ← need sec k (.badCapacity p)
  let t ← needObj t0 p
  let m ← readModelTable t pm (bad .model) (rd .model)
  let c0 ← need t "config" (.badCapacity pc)
  let ct ← needObj c0 pc
  let c ← readWeekAll ct (bad .config) (rd .config)
  return (m, c)

/-- **A learned curve** (`energyOk`): absent is not learned; present is 12 entries below 256. -/
def readEnergyCurve (loc : Loc) (v : Option JVal) : Except Refusal (List (List Char × List Nat)) :=
  match v with
  | none => .ok []
  | some (.arr xs) =>
    if xs.length = 12 then
      match xs.mapM natOf with
      | some ns => if energyOk ns then .ok [(loc.curve, ns)] else .error (.badCurve loc)
      | none => .error (.badCurve loc)
    else .error (.badCurve loc)
  | some _ => .error (.badCurve loc)

/-- `energy`: absent is no learned curve. -/
def readEnergyIn (e0 : JVal) : Except Refusal (List (List Char × List Nat)) := do
  let e ← needObj e0 .energy
  let ol ← opt e "lounge" (.badCurve .lounge)
  let l ← readEnergyCurve .lounge ol
  let oh ← opt e "home" (.badCurve .home)
  let h ← readEnergyCurve .home oh
  return l ++ h

def readEnergy (sec : JVal) : Except Refusal (List (List Char × List Nat)) :=
  match opt sec "energy" (.badCapacity .energy) with
  | .error e => .error e
  | .ok none => .ok []
  | .ok (some e) => readEnergyIn e

/-- **One prior range** (`mkStep?`). -/
def optPair (o : Option JVal) (r : Refusal) : Except Refusal (Option (Nat × Nat)) :=
  match o with
  | none => .ok none
  | some v => (orErr (pairWith natOf v) r).map some

def readStep (key : List Char) (v : JVal) : Except Refusal Step := do
  let f ← pairAt v "from" (.step .badStep key)
  let tv ← opt v "to" (.step .badStep key)
  let t ← optPair tv (.step .badStep key)
  let l ← natAt v "level" (.step .badLevel key)
  (mkStep? f.1 f.2 t l).mapError (fun e => .step e key)

/-- **One prior curve** (`curveOk`): at most 64 ranges, checked before any is read. -/
def readCurve (key : List Char) (v : JVal) : Except Refusal (List Step) :=
  match v with
  | .arr xs =>
    if maxCurveSteps < xs.length then .error (.step .badStep key)
    else
      match xs.mapM (readStep key) with
      | .ok steps => if curveOk steps then .ok steps else .error (.step .badStep key)
      | .error e => .error e
  | _ => .error (.step .badStep key)

/-- The first key carried twice. -/
def firstDupKey : List (List Char) → Option (List Char)
  | [] => none
  | k :: ks => if k ∈ ks then some k else firstDupKey ks

/-- **The prior curves** (`priorOk`), every one of them (L4's disagreement 8). -/
def readPriorEntry (kv : List Char × JVal) : Except Refusal (List Char × List Step) :=
  if maxCurveKey < kv.1.length then .error (.badPrior kv.1)
  else (readCurve kv.1 kv.2).map (fun s => (kv.1, s))

def readPriorObj (kvs : List (List Char × JVal)) : Except Refusal (List (List Char × List Step)) :=
  if maxCurves < kvs.length then .error (.badPrior ((kvs.getD maxCurves ([], .null)).1))
  else
    match kvs.mapM readPriorEntry with
    | .error e => .error e
    | .ok p => if priorOk p then .ok p else .error (.badPrior ((firstDupKey (p.map Prod.fst)).getD []))

def readPrior (sec : JVal) : Except Refusal (List (List Char × List Step)) :=
  match need sec "prior" (.badCapacity .prior) with
  | .ok (.obj kvs) => readPriorObj kvs
  | _ => .error (.badCapacity .prior)

/-- `home_max_ci` (`homeMaxOk`). -/
def readHomeMax (sec : JVal) : Except Refusal Nat :=
  match natAt sec "homeMaxCi" .badCap with
  | .ok n => if homeMaxOk n then .ok n else .error .badCap
  | .error e => .error e

/-- **`[day]`** (`mkDayCfg?`), with the request's `blockMin` as `block_min`. -/
def readDay (bm : Nat) (sec : JVal) : Except Refusal DayCfg := do
  let d0 ← need sec "day" (.badCapacity .day)
  let v ← needObj d0 .day
  let br ← natAt v "breakMin" (.badDay .breakMin)
  let ba ← natAt v "breakAfterBlocks" (.badDay .breakAfterBlocks)
  let ml ← natAt v "minLastBlockMin" (.badDay .minLastBlockMin)
  let wh ← pairAt v "windowHours" (.badDay .windowHours)
  let cap ← clockAt v "windowCap" .badWindowCap
  let rt ← pairAt v "budgetRatio" (.badDay .budgetRatio)
  (mkDayCfg? bm br ba ml wh.1 wh.2 cap rt.1 rt.2).mapError .badDay

/-- The most ladder edges, and the widest denominator of a priority pair (`capDen`'s 18 places). -/
def maxBins : Nat := 16
def maxPairDen : Nat := 1000000000000000000

/-- **The ladder off the wire** (step 2's `binsOfPairs?`): at most 16 edges, each denominator at
most `10^18`. -/
def binsOfWire (xs : List JVal) : Option Bins :=
  if maxBins < xs.length then none
  else (xs.mapM (pairWith natOf)).bind fun ps =>
    if ps.all (fun p => decide (p.2 ≤ maxPairDen)) then binsOfPairs? ps else none

/-- **The safety off the wire** (step 2's `safetyOf?`): a denominator of at most `10^18`, a
safety of at most 1,000. -/
def safetyOfWire (p : Nat × Nat) : Option Arith.Pos :=
  if p.2 ≤ maxPairDen ∧ p.1 ≤ 1000 * p.2 then safetyOf? p.1 p.2 else none

/-- **`[priority]`, through step 2's decoders** (gap 77): `binsOfPairs?`, `safetyOf?` (a safety of
at most 1,000), `defaultPrioOf?`. -/
def readPriority (sec : JVal) : Except Refusal (Bins × Arith.Pos × Fin 4) := do
  let p0 ← need sec "priority" (.badCapacity .priority)
  let v ← needObj p0 .priority
  let xs ← arrAt v "bins" .badBins
  let bins ← orErr (binsOfWire xs) .badBins
  let sp ← pairAt v "safety" .badSafety
  let safety ← orErr (safetyOfWire sp) .badSafety
  let n ← natAt v "defaultPriority" .badDefaultPriority
  let dflt ← orErr (defaultPrioOf? n) .badDefaultPriority
  return (bins, safety, dflt)

/-! ### The zone table: B4's one reader

**Merged 2026-09-14 (gap 108 closed).**  L6 read `tz` with its own fixed-width readers
(`readOffsetText`, `readInstantText`, `transOf`, `readTrans`, `maxTrans`, `tzObj`).  The D9 track's
B4 owns the key (design §14.2) and reads it with `Tm.readTz` (`readTzOffset`, `readTzInstant` through
`LogStamp.parseStamp`, `Cal.mkTz?`), so the merge keeps that one reader (AGENTS §5.3) and this is
only the capacity section's view of it: absent is `tzAbsent`, and a refusal is `badTz` with B4's
name for it. -/

/-- **The zone table**: `tzAbsent`, else `Tm.readTz`'s table or its refusal as `badTz <why>`. -/
def readTz (j : JVal) : Except Refusal Cal.Tz :=
  match jget j "tz" with
  | .ok none => .error .tzAbsent
  | .ok (some z) => (Tm.readTz z).mapError .badTz
  | .error _ => .error (.badTz .shape)

/-! ### The section, whole -/

/-- The section's values, each through its constructor. -/
structure Section where
  pModel    : Cal.Weekday → Option (Nat × Nat)
  pConfig   : Cal.Weekday → Nat × Nat
  arrModel  : Cal.Weekday → Option Field.Clock
  arrConfig : Cal.Weekday → Field.Clock
  wake      : Option WakeClock
  energy    : List (List Char × List Nat)
  prior     : List (List Char × List Step)
  homeMax   : Nat
  day       : DayCfg
  prio      : Bins × Arith.Pos × Fin 4
  days      : Nat
  day0      : List Nat

/-- `wake`: absent or `null` is no logged wake. -/
def readWake (sec : JVal) : Except Refusal (Option WakeClock) :=
  match opt sec "wake" .badWake with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some w) => match natAt w "sec" .badWake, natAt w "ns" .badWake with
    | .ok s, .ok n => .ok (some ⟨s, n⟩)
    | _, _ => .error .badWake

/-- `days`: a natural (its bound is `mkInput?`'s). -/
def readDays (sec : JVal) : Except Refusal Nat := natAt sec "days" (.badCapacity .days)

/-- `day0`: at most six naturals, read (the exact count and bound are `mkInput?`'s). -/
def readDay0 (sec : JVal) : Except Refusal (List Nat) :=
  match arrAt sec "day0" .badDay0 with
  | .ok xs => orErr (if 6 < xs.length then none else xs.mapM natOf) .badDay0
  | .error e => .error e

/-- **The section** (design §13.6), in the order of the example. -/
def readSection (bm : Nat) (cap : JVal) : Except Refusal Section := do
  let sec ← needObj cap .capacity
  let p ← readTables sec "pLounge" .pLounge .pLoungeModel .pLoungeConfig
    (fun s wd => .weight .badWeight s wd) readWeight
  let a ← readTables sec "arrival" .arrival .arrivalModel .arrivalConfig
    (fun s wd => .badClock s wd) readArrival
  let wake ← readWake sec
  let energy ← readEnergy sec
  let prior ← readPrior sec
  let homeMax ← readHomeMax sec
  let day ← readDay bm sec
  let prio ← readPriority sec
  let days ← readDays sec
  let day0 ← readDay0 sec
  return ⟨p.1, p.2, a.1, a.2, wake, energy, prior, homeMax, day, prio, days, day0⟩

/-- The decoded request: the lookahead's raw input and its decoded form, and the priority
configuration for the priority wiring (L8). -/
structure CapReq where
  input  : InputIn
  look   : Input
  bins   : Bins
  safety : Arith.Pos
  dflt   : Fin 4

/-- L5's refusals, named on the wire.  A weight is named by the reading it came from. -/
def ofCapErr (x : InputIn) : CapErr → Refusal
  | .lookaheadTooLong => .lookaheadTooLong
  | .weight wd e => .weight e (if (x.pModel wd).isSome then .model else .config) wd
  | .badWake => .badWake
  | .badDay0 => .badDay0

/-- The lookahead's last day is a date the calendar renders (year ≤ 9999). -/
def lookaheadInCalendar (today days : Nat) : Bool := days == 0 || Field.dayWf (today + days - 1)

/-- The lookahead's raw input from the section, the zone, today and the plan's walls. -/
def Section.input (s : Section) (today bm : Nat) (z : Cal.Tz) (plan : PlanCore) : InputIn :=
  ⟨today, s.days, s.day0, s.pModel, s.pConfig, s.arrModel, s.arrConfig, s.wake, ⟨s.prior, s.energy⟩,
    s.homeMax, s.day, z, wallIndex z bm plan⟩

/-- A lookahead the calendar can render, or `lookaheadTooLong`. -/
def inCalendar (today days : Nat) : Except Refusal Unit :=
  if lookaheadInCalendar today days then .ok () else .error .lookaheadTooLong

/-- **The capacity request**: the clock, the zone, the section, then L5's `mkInput?` over the
loaded plan's walls (`wallIndex`, indexed once, `buffer:` in the request's blocks). -/
def readCapacity (plan : PlanCore) (clock : ReqClock) (j cap : JVal) : Except Refusal CapReq := do
  let today ← orErr clock.now .nowAbsent
  let bm ← orErr (clock.blockMin.map Subtype.val) .blockMinAbsent
  let z ← readTz j
  let s ← readSection bm cap
  let I ← (mkInput? (s.input today bm z plan)).mapError (ofCapErr (s.input today bm z plan))
  let _ ← inCalendar today s.days
  return ⟨s.input today bm z plan, I, s.prio.1, s.prio.2.1, s.prio.2.2⟩

/-- **`readCapacity` over a zone already read** (stage 5 D10 L8, gap 110): the same request, with the
zone handed in instead of read again.  `runCap` reads `tz` once (`zoneOf`) and calls this;
`the_zone_is_read_once_and_feeds_both_sections` is the bridge that carries every `readCapacity` law
to it. -/
def readCapacityZ (plan : PlanCore) (clock : ReqClock) (zo : Option Cal.Tz) (cap : JVal) :
    Except Refusal CapReq := do
  let today ← orErr clock.now .nowAbsent
  let bm ← orErr (clock.blockMin.map Subtype.val) .blockMinAbsent
  let z ← orErr zo .tzAbsent
  let s ← readSection bm cap
  let I ← (mkInput? (s.input today bm z plan)).mapError (ofCapErr (s.input today bm z plan))
  let _ ← inCalendar today s.days
  return ⟨s.input today bm z plan, I, s.prio.1, s.prio.2.1, s.prio.2.2⟩

/-! ### The candidates (stage 5 D10 L8, gaps 80 and 107)

`capacity.candidates` is optional: `{"hysteresis": true, "items": [ … ]}`, at most 1,024 records,
each fork `priority::Candidate`'s §7 inputs as the host collected them (gap 113):

```jsonc
{"id": "a1", "ci": 3, "rootPrio": null, "remaining": 30, "due": "2026-09-08",
 "window": false, "wall": false, "optional": false, "overdue": false, "mandatory": false, "hot": false,
 "yesterday": 6}
```

`rootPrio` (the root's written `!k`, `1..4`), `due` (a date) and `yesterday` (`0..7`) may be absent or
`null`; every other key is required.  A record is refused by its position and key
(`badCandidate <i> <key>`): `ci` above 5 (`levelOf?`), `rootPrio` outside `1..4` (`defaultPrioOf?`),
`remaining` above `2^32 − 1` (fork `u32`), a `due` that is not a date (`Field.parseDate`), `yesterday`
above 7 (`yesterdayOf?`), an `id` over 1,024 characters, or a key of the wrong JSON type. -/

/-- A JSON boolean at `k`, or `r`. -/
def boolAt (v : JVal) (k : String) (r : Refusal) : Except Refusal Bool :=
  match need v k r with
  | .ok (.bool b) => .ok b
  | _ => .error r

/-- An optional natural at `k` through its decoder: absent or `null` is `none`. -/
def optNatWith {α : Type} (v : JVal) (k : String) (r : Refusal) (dec : Nat → Option α) :
    Except Refusal (Option α) :=
  match opt v k r with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some (.num n)) => match dec n with
    | some a => .ok (some a)
    | none => .error r
  | .ok (some _) => .error r

/-- An optional date at `due`. -/
def readDueDate (v : JVal) (r : Refusal) : Except Refusal (Option Day) :=
  match opt v "due" r with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some (.str s)) => match Field.parseDate s with
    | some d => .ok (some d)
    | none => .error r
  | .ok (some _) => .error r

/-- The most candidates a request carries, the longest id, the largest remaining (fork `u32`). -/
def maxCandidates : Nat := 1024
def maxCandId : Nat := 1024
def maxRemaining : Nat := 4294967295

/-- A bound, or `r`. -/
def within (b : Bool) (r : Refusal) : Except Refusal Unit := if b then .ok () else .error r

/-- **One candidate record**, every value through its decoder. -/
def readCand (i : Nat) (v : JVal) : Except Refusal Look.Cand := do
  let id ← strAt v "id" (.badCandidate i .id)
  let _ ← within (decide (id.length ≤ maxCandId)) (.badCandidate i .id)
  let ciN ← natAt v "ci" (.badCandidate i .ci)
  let ci ← orErr (levelOf? ciN) (.badCandidate i .ci)
  let rp ← optNatWith v "rootPrio" (.badCandidate i .rootPrio) defaultPrioOf?
  let rem ← natAt v "remaining" (.badCandidate i .remaining)
  let _ ← within (decide (rem ≤ maxRemaining)) (.badCandidate i .remaining)
  let due ← readDueDate v (.badCandidate i .due)
  let window ← boolAt v "window" (.badCandidate i .window)
  let wall ← boolAt v "wall" (.badCandidate i .wall)
  let optional ← boolAt v "optional" (.badCandidate i .optional)
  let overdue ← boolAt v "overdue" (.badCandidate i .overdue)
  let mandatory ← boolAt v "mandatory" (.badCandidate i .mandatory)
  let hot ← boolAt v "hot" (.badCandidate i .hot)
  let y ← optNatWith v "yesterday" (.badCandidate i .yesterday) yesterdayOf?
  return ⟨id, ci, rp, rem, due, window, wall, optional, overdue, mandatory, hot, y⟩

/-- **A record's floor** (stage 5 D10 L8 host half, gap 79): absent or `null` is none; otherwise an
object with `left` (minutes, at most `2^32 − 1`, fork `u32`) and `until` (a date), else
`badCandidate <i> floor`. -/
def readFloor (i : Nat) (v : JVal) : Except Refusal (Option Look.Floor) :=
  match opt v "floor" (.badCandidate i .floor) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some f) =>
    match natAt f "left" (.badCandidate i .floor), need f "until" (.badCandidate i .floor) with
    | .ok l, .ok (.str d) =>
      if l ≤ maxRemaining then
        match Field.parseDate d with
        | some day => .ok (some ⟨l, day⟩)
        | none => .error (.badCandidate i .floor)
      else .error (.badCandidate i .floor)
    | _, _ => .error (.badCandidate i .floor)

/-- One record: the candidate, then its floor. -/
def readCandFloor (i : Nat) (v : JVal) : Except Refusal (Look.Cand × Option Look.Floor) := do
  let c ← readCand i v
  let f ← readFloor i v
  return (c, f)

/-- The decoded `candidates` object: each candidate with its floor. -/
structure CandReq where
  hysteresis : Bool
  items      : List (Look.Cand × Option Look.Floor)

/-- The candidates of a decoded object. -/
def CandReq.cands (q : CandReq) : List Look.Cand := q.items.map Prod.fst

/-- The records, each read at its position (after the count's guard). -/
def readCandList (xs : List JVal) : Except Refusal (List (Look.Cand × Option Look.Floor)) :=
  xs.zipIdx.mapM (fun p => readCandFloor p.2 p.1)

/-- **`capacity.candidates`**: absent is no grants; present is `hysteresis`, then at most 1,024 `items`,
each read by `readCand`. -/
def readCands (cap : JVal) : Except Refusal (Option CandReq) :=
  match opt cap "candidates" (.badCapacity .candidates) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some v) =>
    match boolAt v "hysteresis" (.badCapacity .candidates) with
    | .error e => .error e
    | .ok hy =>
      match arrAt v "items" (.badCapacity .candidates) with
      | .error e => .error e
      | .ok xs =>
        if maxCandidates < xs.length then .error .tooManyCandidates
        else (readCandList xs).map (fun cs => some ⟨hy, cs⟩)

/-! ### The response -/

/-- **A unit count as a digit string** (D17). -/
def unitsJson (n : Nat) : JVal := .str (digitsOf n)

/-- One day: its date and its six numerators over `den`, level 0 first. -/
def dayCapJson (c : DayCapacity) : JVal :=
  .obj [("day".toList, .str (Field.renderDate c.day)),
    ("numAt".toList, .arr [unitsJson (c.numAt 0), unitsJson (c.numAt 1), unitsJson (c.numAt 2),
      unitsJson (c.numAt 3), unitsJson (c.numAt 4), unitsJson (c.numAt 5)])]

/-- The days the response carries (design D10-8). -/
def maxEmittedDays : Nat := 7

/-- **The `lookahead` key**: `den`, then the first `min(days, 7)` days. -/
def lookaheadJson (cs : List DayCapacity) : JVal :=
  .obj [("den".toList, unitsJson capDen), ("days".toList, .arr ((cs.take maxEmittedDays).map dayCapJson))]

/-- The `ok` object with `lookahead` after its keys. -/
def withLookahead (r v : JVal) : JVal :=
  match r with
  | .obj [(k, .obj kvs)] => .obj [(k, .obj (kvs ++ [("lookahead".toList, v)]))]
  | _ => r

/-- An optional natural: `null` when absent. -/
def optNatJson : Option Nat → JVal
  | none => .null
  | some n => .num n

/-- §7.1's bin as fork `Prio::bin` writes it: `+n` is `n`; HOT, or no pass, is `null`. -/
def binJson : Option Arith.Bin → JVal
  | some (.plus n) => .num n
  | _ => .null

/-- Fork `PrioClass`'s serde names. -/
def pclassName : Look.PClass → List Char
  | .wall => "wall".toList | .hot => "hot".toList | .impossible => "impossible".toList
  | .overdue => "overdue".toList | .mandatory => "mandatory".toList | .hotFlag => "hotflag".toList
  | .dated => "dated".toList | .rank => "rank".toList | .optional => "optional".toList

/-- **One candidate's grant** (design §13.6, stage 5 D10 L8): `id`, `class`, `k`, `p`, `rawP`, `need` (minutes,
R1's ceiling), `until` (the due date, when the candidate entered the pass), then `avail`, `allocation`
and `shortfall` in units over `den` (digit strings, D17), then `bin`. -/
def grantJson (o : Look.CandOut) : JVal :=
  .obj [("id".toList, .str o.cand.id), ("class".toList, .str (pclassName o.cls)), ("k".toList, .num o.k),
    ("p".toList, optNatJson o.p), ("rawP".toList, optNatJson o.raw), ("need".toList, .num o.need),
    ("until".toList, match o.grant with
      | some g => .str (Field.renderDate g.deadline.due)
      | none => .null),
    ("avail".toList, unitsJson ((o.grant.map Grant.avail).getD 0)),
    ("allocation".toList, unitsJson ((o.grant.map Grant.reserved).getD 0)),
    ("shortfall".toList, unitsJson o.shortfall), ("bin".toList, binJson o.bin)]

/-- **A floor answer's grant** (stage 5 D10 L8 host half, gap 79): the keys of `grantJson`, the class
`floor` for a floor's `+n` row (fork `PrioClass::Floor`), `until` the floor's last date, `avail` what the
pass left, `allocation` `min(need, avail)` (fork `floor_pass`; a floor reserves nothing), `shortfall`
`need − avail` when HOT.  An answer without a floor is `grantJson`'s. -/
def grantJsonF (o : Look.FloorOut) : JVal :=
  match o.floor with
  | none => grantJson o.out
  | some g =>
    .obj [("id".toList, .str o.out.cand.id),
      ("class".toList, .str (if o.cls = .dated then "floor".toList else pclassName o.cls)),
      ("k".toList, .num o.out.k), ("p".toList, optNatJson o.out.p), ("rawP".toList, optNatJson o.out.raw),
      ("need".toList, .num o.out.need), ("until".toList, .str (Field.renderDate g.floor.last)),
      ("avail".toList, unitsJson g.avail), ("allocation".toList, unitsJson (min (g.need * capDen) g.avail)),
      ("shortfall".toList, unitsJson o.shortfall), ("bin".toList, binJson o.out.bin)]

/-- An answer without a floor emits `grantJson`'s bytes. -/
theorem grantJsonF_without_a_floor (o : Look.CandOut) : grantJsonF ⟨o, none⟩ = grantJson o := rfl

/-- The grants of a request's candidates over its whole lookahead (not only the seven days emitted),
the floor pass included. -/
def grantsOf (c : CapReq) (la : List DayCapacity) (q : CandReq) : List Look.FloorOut :=
  Look.prioritiesWithFloors c.bins c.safety c.dflt q.hysteresis la q.items

/-- **The `lookahead` key** (stage 5 D10 L8): L6's `den` and `days`, then `grants` when the request
carried `candidates`.  The lookahead is computed once for both. -/
def lookaheadJsonWith (c : CapReq) (q : Option CandReq) : JVal :=
  let la := Look.lookahead c.look
  match q with
  | none => lookaheadJson la
  | some q => .obj [("den".toList, unitsJson capDen), ("days".toList, .arr ((la.take maxEmittedDays).map dayCapJson)),
      ("grants".toList, .arr ((grantsOf c la q).map grantJsonF))]

end CapWire

/-- The `log` answer after `report`, when the request carries a `log` section (B4's `withLog`). -/
def logInto : Option VLogReq → JVal → JVal
  | none, r => r
  | some l, r => withLog (logAnswer l) r

/-- **The zone, read once** (stage 5 D10 L8, gap 110): absent, a table, or B4's refusal in the `log`
shape (`readLogSection`'s names and order). -/
def zoneOf (j : JVal) : Except JVal (Option Cal.Tz) :=
  match jget j "tz" with
  | .error _ => .error (LogRefusal.badTz .shape).json
  | .ok none => .ok none
  | .ok (some z) =>
    match readTz z with
    | .error w => .error (LogRefusal.badTz w).json
    | .ok t => .ok (some t)

/-- **The `log` section over a zone already read** (gap 110): `readLogSection` after its zone check
(`readLogSection_is_zoneOf_then_logSectionWith`). -/
def logSectionWith (j : JVal) (zo : Option Cal.Tz) : Except JVal (Option VLogReq) :=
  match jget j "log" with
  | .ok none => .ok none
  | .ok (some l) =>
    if zo.isNone then .error LogRefusal.tzAbsent.json
    else
      match readLogReq l with
      | .ok r => .ok (some r)
      | .error e => .error e.json
  | .error _ => .error (LogRefusal.badLogReq .log).json

open CapWire in
/-- **A capacity request, after its one zone reading**: the `log` section over that zone, the
documents (`runLoad`), the capacity section over that zone (`readCapacityZ`), the candidates
(`readCands`), then **no commands** (gap 109: the walls are the documents as sent, so a request that
also edits them is refused by name, `capacityWithCommands`), and the answer: `run`'s documents and
report, `log` when asked, then `lookahead` with its grants when candidates were sent. -/
def runCapZ (j cap : JVal) (zo : Option Cal.Tz) : Except JVal JVal :=
  match logSectionWith j zo with
  | .error e => .error e
  | .ok lg =>
  match runLoad j with
  | .error e => .error e
  | .ok (plan, cmds, clock) =>
    match readCapacityZ plan.val clock zo cap with
    | .error r => .error (refusalJson r)
    | .ok c =>
      match readCands cap with
      | .error r => .error (refusalJson r)
      | .ok q =>
        match cmds with
        | _ :: _ => .error (refusalJson .capacityWithCommands)
        | [] =>
          match runPlan plan [] with
          | .error e => .error e
          | .ok r => .ok (withLookahead (logInto lg r) (lookaheadJsonWith c q))

open CapWire in
/-- **The request, with its capacity section**: without `capacity`, B4's `runWithLog`
(`runCap_without_capacity_is_runWithLog`, and `run` when there is no `log` section either); with it,
the zone is read once (`zoneOf`, gap 110) and `runCapZ` answers over it: the `log` section's refusals
come first (B4's rule), the documents load, the capacity section is read, the candidates, no commands
(gap 109), and the response gains `log` (when asked) and then `lookahead` (design §10.2's order).
**Merged 2026-09-14** with the D9 track's B4: L6's `runCap` called `run` and so dropped a `log`
section.  **Stage 5 D10 L8**: one zone reading, grants, and the commands refusal. -/
def runCap (j : JVal) : Except JVal JVal :=
  match jget j "capacity" with
  | .error e => .error (jsonErr e)
  | .ok none => runWithLog j
  | .ok (some cap) =>
    match zoneOf j with
    | .error e => .error e
    | .ok zo => runCapZ j cap zo

/-- **The response value for a request's bytes**, `respond` over `runCap`. -/
def respondCap (input : List Char) : JVal :=
  match jparse input with
  | .error e => jsonErr s!"bad json: {jerrText e}"
  | .ok j =>
    match runCap j with
    | .error e => e
    | .ok r    => r

/-- What the FFI runs: `call` over `respondCap`. -/
def callCap (input : String) : String := String.ofList (jemit (respondCap input.toList))

/-- **The one export** (R9), moved here from `call`'s definition at step L6. -/
@[export tm_kernel_call]
def callExport (input : String) : String := callCap input

/-! ### The laws: the bridge to `run`, what an answered request satisfies, and the response -/

theorem capBind_ok_elim {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-! #### Stage 5 D10 L8, gap 110: the zone is read once, and that reading feeds both sections -/

/-- **`readLogSection` is the one zone reading, then the `log` section over it.** -/
theorem readLogSection_is_zoneOf_then_logSectionWith (kvs : List (List Char × JVal)) :
    readLogSection (.obj kvs) = (match zoneOf (.obj kvs) with
      | .error e => .error e
      | .ok zo => logSectionWith (.obj kvs) zo) := by
  unfold readLogSection zoneOf logSectionWith
  cases jget (.obj kvs) "tz" with
  | error _ => rfl
  | ok tz =>
    cases tz with
    | none => rfl
    | some z =>
      cases ht : readTz z with
      | error w => simp only [Option.map_some, ht]
      | ok t => simp only [Option.map_some, ht, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]

theorem zoneOf_ok_obj {j : JVal} {zo : Option Cal.Tz} (h : zoneOf j = .ok zo) : ∃ kvs, j = .obj kvs := by
  cases j <;> first | exact ⟨_, rfl⟩ | simp [zoneOf, jget] at h

/-- **Gap 110, closed: one zone reading feeds both sections.**  Whenever the zone reads, B4's `log`
section is `logSectionWith` over that reading, and L6's `readCapacity` is `readCapacityZ` over the same
reading, so every law of either function holds of what `runCap` runs. -/
theorem the_zone_is_read_once_and_feeds_both_sections {j : JVal} {zo : Option Cal.Tz} (h : zoneOf j = .ok zo) :
    readLogSection j = logSectionWith j zo ∧
      ∀ plan clock cap, CapWire.readCapacity plan clock j cap = CapWire.readCapacityZ plan clock zo cap := by
  obtain ⟨kvs, rfl⟩ := zoneOf_ok_obj h
  refine ⟨by rw [readLogSection_is_zoneOf_then_logSectionWith, h], fun plan clock cap => ?_⟩
  have hz : CapWire.readTz (.obj kvs) = CapWire.orErr zo .tzAbsent := by
    unfold zoneOf at h
    unfold CapWire.readTz CapWire.orErr
    cases hj : jget (.obj kvs) "tz" with
    | error _ => simp [hj] at h
    | ok tz =>
      cases tz with
      | none =>
        simp only [hj, Except.ok.injEq] at h
        subst h
        rfl
      | some z =>
        cases ht : readTz z with
        | error w => simp [hj, ht] at h
        | ok t =>
          simp only [hj, ht, Except.ok.injEq] at h
          subst h
          simp only [ht, Except.mapError]
  unfold CapWire.readCapacity CapWire.readCapacityZ
  rw [hz]

/-- **A capacity request is `runCapZ` over its one zone reading.** -/
theorem runCap_with_capacity_reads_the_zone_once {j cap : JVal} (hc : jget j "capacity" = .ok (some cap)) :
    runCap j = (match zoneOf j with
      | .error e => .error e
      | .ok zo => runCapZ j cap zo) := by
  unfold runCap
  rw [hc]

theorem zoneOf_of_readLogSection {j cap : JVal} {lg : Option VLogReq} (hc : jget j "capacity" = .ok (some cap))
    (hg : readLogSection j = .ok lg) : ∃ zo, zoneOf j = .ok zo ∧ logSectionWith j zo = .ok lg := by
  obtain ⟨kvs, rfl⟩ : ∃ kvs, j = .obj kvs := by
    cases j <;> first | exact ⟨_, rfl⟩ | simp [jget] at hc
  rw [readLogSection_is_zoneOf_then_logSectionWith] at hg
  cases hz : zoneOf (.obj kvs) with
  | error e => rw [hz] at hg; cases hg
  | ok zo => rw [hz] at hg; exact ⟨zo, rfl, hg⟩

/-- **A request without `capacity` is `runWithLog`'s**, byte for byte (merged form: L6 stated
`runCap j = run j`, which the merge made false for a request with a `log` section). -/
theorem runCap_without_capacity_is_runWithLog {j : JVal} (h : jget j "capacity" = .ok none) :
    runCap j = runWithLog j := by
  simp [runCap, h]

/-- **A request without `capacity` or a `log` section is `run`'s**, byte for byte. -/
theorem runCap_without_capacity_is_run {j : JVal} (h : jget j "capacity" = .ok none)
    (hl : readLogSection j = .ok none) : runCap j = run j := by
  rw [runCap_without_capacity_is_runWithLog h, runWithLog_without_a_log_is_run j hl]

/-- **At the bytes**: a request that parses to a value without `capacity` gets `respond`'s answer. -/
theorem respondCap_without_capacity_is_respond (input : List Char)
    (h : ∀ j, jparse input = .ok j → jget j "capacity" = .ok none) : respondCap input = respond input := by
  unfold respondCap respond
  cases hp : jparse input with
  | error e => rfl
  | ok j => dsimp only; rw [runCap_without_capacity_is_runWithLog (h j hp)]; try rfl

/-- **The exported function is `call` on every request without `capacity`**, so every theorem stated
about `call` above holds of the FFI for those requests. -/
theorem callExport_without_capacity_is_call (input : String)
    (h : ∀ j, jparse input.toList = .ok j → jget j "capacity" = .ok none) : callExport input = call input := by
  unfold callExport callCap call
  rw [respondCap_without_capacity_is_respond _ h]

/-- **J5's round trip, at the exported function**: whatever bytes the FFI hands the host, the
kernel's own parser reads back to exactly the response value `respondCap` built. -/
theorem the_exported_call_emits_parses_back (input : String) :
    jparse (callExport input).toList = .ok (respondCap input.toList) := by
  unfold callExport callCap
  rw [String.toList_ofList]
  exact jparse_jemit _

/-- **With `capacity` and candidates** (stage 5 D10 L8): the zone reads once, the documents load, the
section and the candidates are read, there are no commands, and the answer is `run`'s with `log`
(when asked) and then `lookahead`, its grants included when candidates were sent. -/
theorem runCap_answers_with_the_lookahead_and_grants {j cap : JVal} {lg : Option VLogReq} {plan : WfPlan}
    {cmds : List ReqCmd} {clock : ReqClock} {c : CapWire.CapReq} {q : Option CapWire.CandReq} {r : JVal}
    (hc : jget j "capacity" = .ok (some cap)) (hg : readLogSection j = .ok lg)
    (hl : runLoad j = .ok (plan, cmds, clock)) (hr : CapWire.readCapacity plan.val clock j cap = .ok c)
    (hq : CapWire.readCands cap = .ok q) (hcm : cmds = []) (hp : runPlan plan cmds = .ok r) :
    runCap j = .ok (CapWire.withLookahead (logInto lg r) (CapWire.lookaheadJsonWith c q)) := by
  subst hcm
  obtain ⟨zo, hz, hlw⟩ := zoneOf_of_readLogSection hc hg
  rw [(the_zone_is_read_once_and_feeds_both_sections hz).2] at hr
  rw [runCap_with_capacity_reads_the_zone_once hc, hz]
  simp only [runCapZ, hlw, hl, hr, hq, hp]

/-- **With `capacity`**: the documents load, the section is read, and the answer is `run`'s with
`lookahead` after its keys.  Stage 5 D10 L8 added the two hypotheses the new wire needs: no
`candidates` (`hq`; with them, `runCap_answers_with_the_lookahead_and_grants`) and no commands
(`hcm`; with them, `runCap_refuses_commands_beside_capacity`, gap 109). -/
theorem runCap_answers_with_the_lookahead {j cap : JVal} {lg : Option VLogReq} {plan : WfPlan}
    {cmds : List ReqCmd} {clock : ReqClock} {c : CapWire.CapReq} {r : JVal} (hc : jget j "capacity" = .ok (some cap))
    (hg : readLogSection j = .ok lg)
    (hl : runLoad j = .ok (plan, cmds, clock)) (hr : CapWire.readCapacity plan.val clock j cap = .ok c)
    (hq : CapWire.readCands cap = .ok none) (hcm : cmds = [])
    (hp : runPlan plan cmds = .ok r) :
    runCap j = .ok (CapWire.withLookahead (logInto lg r) (CapWire.lookaheadJson (Look.lookahead c.look))) :=
  runCap_answers_with_the_lookahead_and_grants hc hg hl hr hq hcm hp

/-- **With `capacity`, a refused `tz` or `log` section refuses the request first** (B4's rule, kept
by the merge), before the documents load. -/
theorem runCap_refuses_a_log_section_first {j cap e : JVal} (hc : jget j "capacity" = .ok (some cap))
    (hg : readLogSection j = .error e) : runCap j = .error e := by
  obtain ⟨kvs, rfl⟩ : ∃ kvs, j = .obj kvs := by
    cases j <;> first | exact ⟨_, rfl⟩ | simp [jget] at hc
  rw [runCap_with_capacity_reads_the_zone_once hc]
  rw [readLogSection_is_zoneOf_then_logSectionWith] at hg
  cases hz : zoneOf (.obj kvs) with
  | error e' => rw [hz] at hg; simp only [Except.error.injEq] at hg ⊢; exact hg
  | ok zo => rw [hz] at hg; simp only at hg ⊢; simp only [runCapZ, hg]

/-- **A refused section refuses the request by its name**, whatever the commands. -/
theorem runCap_refuses_what_the_section_refuses {j cap : JVal} {lg : Option VLogReq} {plan : WfPlan}
    {cmds : List ReqCmd} {clock : ReqClock} {e : CapWire.Refusal} (hc : jget j "capacity" = .ok (some cap))
    (hg : readLogSection j = .ok lg)
    (hl : runLoad j = .ok (plan, cmds, clock)) (hr : CapWire.readCapacity plan.val clock j cap = .error e) :
    runCap j = .error (CapWire.refusalJson e) := by
  obtain ⟨zo, hz, hlw⟩ := zoneOf_of_readLogSection hc hg
  rw [(the_zone_is_read_once_and_feeds_both_sections hz).2] at hr
  rw [runCap_with_capacity_reads_the_zone_once hc, hz]
  simp only [runCapZ, hlw, hl, hr]

/-- **A refused candidate refuses the request by its name** (stage 5 D10 L8), whatever the commands. -/
theorem runCap_refuses_what_the_candidates_refuse {j cap : JVal} {lg : Option VLogReq} {plan : WfPlan}
    {cmds : List ReqCmd} {clock : ReqClock} {c : CapWire.CapReq} {e : CapWire.Refusal}
    (hc : jget j "capacity" = .ok (some cap)) (hg : readLogSection j = .ok lg)
    (hl : runLoad j = .ok (plan, cmds, clock)) (hr : CapWire.readCapacity plan.val clock j cap = .ok c)
    (hq : CapWire.readCands cap = .error e) :
    runCap j = .error (CapWire.refusalJson e) := by
  obtain ⟨zo, hz, hlw⟩ := zoneOf_of_readLogSection hc hg
  rw [(the_zone_is_read_once_and_feeds_both_sections hz).2] at hr
  rw [runCap_with_capacity_reads_the_zone_once hc, hz]
  simp only [runCapZ, hlw, hl, hr, hq]

/-- **Gap 109's rule, as a refusal** (stage 5 D10 L8): the lookahead's walls are the documents as sent,
so a capacity request that also carries commands is refused by name, `capacityWithCommands`, once its
zone, `log` section, documents, capacity section and candidates have read. -/
theorem runCap_refuses_commands_beside_capacity {j cap : JVal} {lg : Option VLogReq} {plan : WfPlan}
    {cmd : ReqCmd} {cmds : List ReqCmd} {clock : ReqClock} {c : CapWire.CapReq} {q : Option CapWire.CandReq}
    (hc : jget j "capacity" = .ok (some cap)) (hg : readLogSection j = .ok lg)
    (hl : runLoad j = .ok (plan, cmd :: cmds, clock)) (hr : CapWire.readCapacity plan.val clock j cap = .ok c)
    (hq : CapWire.readCands cap = .ok q) :
    runCap j = .error (CapWire.refusalJson .capacityWithCommands) := by
  obtain ⟨zo, hz, hlw⟩ := zoneOf_of_readLogSection hc hg
  rw [(the_zone_is_read_once_and_feeds_both_sections hz).2] at hr
  rw [runCap_with_capacity_reads_the_zone_once hc, hz]
  simp only [runCapZ, hlw, hl, hr, hq]

/-- **Gap 109's rule, as a theorem** (stage 5 D10 L8): every answered capacity request carried no
commands, so the lookahead and its grants are always of the documents the response returns. -/
theorem an_answered_capacity_request_has_no_commands {j cap a : JVal} {plan : WfPlan} {cmds : List ReqCmd}
    {clock : ReqClock} (hc : jget j "capacity" = .ok (some cap)) (hl : runLoad j = .ok (plan, cmds, clock))
    (ha : runCap j = .ok a) : cmds = [] := by
  rw [runCap_with_capacity_reads_the_zone_once hc] at ha
  cases hz : zoneOf j with
  | error e => rw [hz] at ha; cases ha
  | ok zo =>
    rw [hz] at ha
    simp only [runCapZ, hl] at ha
    cases hlw : logSectionWith j zo with
    | error e => rw [hlw] at ha; cases ha
    | ok lg =>
      rw [hlw] at ha
      simp only at ha
      cases hr : CapWire.readCapacityZ plan.val clock zo cap with
      | error e => rw [hr] at ha; cases ha
      | ok c =>
        rw [hr] at ha
        simp only at ha
        cases hq : CapWire.readCands cap with
        | error e => rw [hq] at ha; cases ha
        | ok q =>
          rw [hq] at ha
          cases cmds with
          | nil => rfl
          | cons _ _ => cases ha

/-- `runPlan`'s `ok` is the documents, then the report.  (L6 named it `runPlan_ok_shape`; B4 took
that name for the weaker `∃ kvs` form, so the merge renamed this one.) -/
theorem runPlan_ok_is_docs_then_report {plan : WfPlan} {cmds : List ReqCmd} {r : JVal} (h : runPlan plan cmds = .ok r) :
    ∃ d rep, r = jone "ok" (.obj [("docs".toList, d), ("report".toList, rep)]) := by
  unfold runPlan at h
  cases ha : applyAllR cmds plan with
  | error k => simp [ha, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | ok qr =>
    obtain ⟨q, rp⟩ := qr
    simp only [ha, bind, Except.bind, pure, Except.pure] at h
    cases h
    exact ⟨_, _, rfl⟩

/-- **Build order** (design §10.2): `docs`, `report`, then `lookahead`.  Stage 5 D10 L8: no candidates,
no commands (`hq`, `hcm`). -/
theorem runCap_answers_docs_report_lookahead {j cap : JVal} {plan : WfPlan} {cmds : List ReqCmd}
    {clock : ReqClock} {c : CapWire.CapReq} {r : JVal} (hc : jget j "capacity" = .ok (some cap))
    (hg : readLogSection j = .ok none)
    (hl : runLoad j = .ok (plan, cmds, clock)) (hr : CapWire.readCapacity plan.val clock j cap = .ok c)
    (hq : CapWire.readCands cap = .ok none) (hcm : cmds = [])
    (hp : runPlan plan cmds = .ok r) :
    ∃ d rep, runCap j = .ok (jone "ok" (.obj [("docs".toList, d), ("report".toList, rep),
      ("lookahead".toList, CapWire.lookaheadJson (Look.lookahead c.look))])) := by
  obtain ⟨d, rep, rfl⟩ := runPlan_ok_is_docs_then_report hp
  exact ⟨d, rep, runCap_answers_with_the_lookahead hc hg hl hr hq hcm hp⟩

/-- **Build order with a `log` section** (design §10.2, merged): `docs`, `report`, `log`, then
`lookahead`.  Stage 5 D10 L8: no candidates, no commands (`hq`, `hcm`). -/
theorem runCap_answers_docs_report_log_lookahead {j cap : JVal} {l : VLogReq} {plan : WfPlan}
    {cmds : List ReqCmd} {clock : ReqClock} {c : CapWire.CapReq} {r : JVal} (hc : jget j "capacity" = .ok (some cap))
    (hg : readLogSection j = .ok (some l))
    (hl : runLoad j = .ok (plan, cmds, clock)) (hr : CapWire.readCapacity plan.val clock j cap = .ok c)
    (hq : CapWire.readCands cap = .ok none) (hcm : cmds = [])
    (hp : runPlan plan cmds = .ok r) :
    ∃ d rep, runCap j = .ok (jone "ok" (.obj [("docs".toList, d), ("report".toList, rep),
      ("log".toList, logAnswer l), ("lookahead".toList, CapWire.lookaheadJson (Look.lookahead c.look))])) := by
  obtain ⟨d, rep, rfl⟩ := runPlan_ok_is_docs_then_report hp
  exact ⟨d, rep, runCap_answers_with_the_lookahead hc hg hl hr hq hcm hp⟩

/-- **Build order with grants and floors** (design §10.2, §13.6; stage 5 D10 L8, host half): `docs`,
`report`, `log` when asked, then `lookahead` with `den`, `days` and `grants`, one grant per candidate in
request order, each answered with its floor (`Look.prioritiesWithFloors`, gap 79). -/
theorem runCap_answers_docs_report_lookahead_floor_grants {j cap : JVal} {lg : Option VLogReq} {plan : WfPlan}
    {cmds : List ReqCmd} {clock : ReqClock} {c : CapWire.CapReq} {q : CapWire.CandReq} {r : JVal}
    (hc : jget j "capacity" = .ok (some cap)) (hg : readLogSection j = .ok lg)
    (hl : runLoad j = .ok (plan, cmds, clock)) (hr : CapWire.readCapacity plan.val clock j cap = .ok c)
    (hq : CapWire.readCands cap = .ok (some q)) (hcm : cmds = []) (hp : runPlan plan cmds = .ok r) :
    ∃ d rep, runCap j = .ok (jone "ok" (.obj ([("docs".toList, d), ("report".toList, rep)] ++
      (match lg with | none => [] | some l => [("log".toList, logAnswer l)]) ++
      [("lookahead".toList, .obj [("den".toList, CapWire.unitsJson Look.capDen),
        ("days".toList, .arr (((Look.lookahead c.look).take CapWire.maxEmittedDays).map CapWire.dayCapJson)),
        ("grants".toList, .arr ((Look.prioritiesWithFloors c.bins c.safety c.dflt q.hysteresis (Look.lookahead c.look)
          q.items).map CapWire.grantJsonF))])]))) ∧
      ((Look.prioritiesWithFloors c.bins c.safety c.dflt q.hysteresis (Look.lookahead c.look) q.items).map
        CapWire.grantJsonF).length = q.items.length := by
  obtain ⟨d, rep, rfl⟩ := runPlan_ok_is_docs_then_report hp
  refine ⟨d, rep, ?_, by simp [Look.prioritiesWithFloors_length]⟩
  rw [runCap_answers_with_the_lookahead_and_grants hc hg hl hr hq hcm hp]
  cases lg <;> rfl

/-- **Build order with grants** (design §10.2, §13.6; stage 5 D10 L8): `docs`, `report`, `log` when
asked, then `lookahead` with `den`, `days` and `grants`, one grant per candidate in request order.
Stage 5 D10 L8's host half added `hf` (no candidate carries a floor): with floors, the grants are
`runCap_answers_docs_report_lookahead_floor_grants`'. -/
theorem runCap_answers_docs_report_lookahead_grants {j cap : JVal} {lg : Option VLogReq} {plan : WfPlan}
    {cmds : List ReqCmd} {clock : ReqClock} {c : CapWire.CapReq} {q : CapWire.CandReq} {r : JVal}
    (hc : jget j "capacity" = .ok (some cap)) (hg : readLogSection j = .ok lg)
    (hl : runLoad j = .ok (plan, cmds, clock)) (hr : CapWire.readCapacity plan.val clock j cap = .ok c)
    (hq : CapWire.readCands cap = .ok (some q)) (hcm : cmds = []) (hp : runPlan plan cmds = .ok r)
    (hf : ∀ cf ∈ q.items, cf.2 = none) :
    ∃ d rep, runCap j = .ok (jone "ok" (.obj ([("docs".toList, d), ("report".toList, rep)] ++
      (match lg with | none => [] | some l => [("log".toList, logAnswer l)]) ++
      [("lookahead".toList, .obj [("den".toList, CapWire.unitsJson Look.capDen),
        ("days".toList, .arr (((Look.lookahead c.look).take CapWire.maxEmittedDays).map CapWire.dayCapJson)),
        ("grants".toList, .arr ((Look.priorities c.bins c.safety c.dflt q.hysteresis (Look.lookahead c.look)
          q.cands).map CapWire.grantJson))])]))) ∧
      ((Look.priorities c.bins c.safety c.dflt q.hysteresis (Look.lookahead c.look) q.cands).map CapWire.grantJson).length
        = q.cands.length := by
  obtain ⟨d, rep, h1, -⟩ := runCap_answers_docs_report_lookahead_floor_grants hc hg hl hr hq hcm hp
  refine ⟨d, rep, ?_, by simp [Look.priorities_length]⟩
  rw [h1, Look.prioritiesWithFloors_without_floors _ _ _ _ _ _ hf, List.map_map]
  rfl

namespace CapWire

open Look

/-- **Every unit count reads back** as the host reads a digit string (D17). -/
theorem unitsJson_reads_back (n : Nat) : ∃ s, unitsJson n = .str s ∧ readNat s = some n :=
  ⟨digitsOf n, rfl, readNat_digitsOf n⟩

/-- **The response carries the first `min(days, 7)` days**, in order, each with its six numerators. -/
theorem lookaheadJson_days (cs : List DayCapacity) :
    lookaheadJson cs = .obj [("den".toList, unitsJson capDen),
      ("days".toList, .arr ((cs.take maxEmittedDays).map dayCapJson))] ∧
    (cs.take maxEmittedDays).length = min cs.length 7 := by
  simp [lookaheadJson, maxEmittedDays, Nat.min_comm]

/-! #### What each reader's success means -/

theorem readWeight_ok {src : Src} {wd : Cal.Weekday} {v : JVal} {p : Nat × Nat}
    (h : readWeight src wd v = .ok p) : ∃ w, mkWeight? p.1 p.2 = .ok w := by
  unfold readWeight at h
  split at h
  · cases h
  · rename_i n d _
    split at h
    · rename_i w hw; cases h; exact ⟨w, hw⟩
    · cases h

theorem readWeekAll_ok {α : Type} {tbl : JVal} {bad : Cal.Weekday → Refusal}
    {rd : Cal.Weekday → JVal → Except Refusal α} {f : Cal.Weekday → α}
    (h : readWeekAll tbl bad rd = .ok f) : ∀ wd, ∃ v, rd wd v = .ok (f wd) := by
  unfold readWeekAll at h
  obtain ⟨a1, h1, h⟩ := capBind_ok_elim h
  obtain ⟨a2, h2, h⟩ := capBind_ok_elim h
  obtain ⟨a3, h3, h⟩ := capBind_ok_elim h
  obtain ⟨a4, h4, h⟩ := capBind_ok_elim h
  obtain ⟨a5, h5, h⟩ := capBind_ok_elim h
  obtain ⟨a6, h6, h⟩ := capBind_ok_elim h
  obtain ⟨a7, h7, h⟩ := capBind_ok_elim h
  cases h
  have one : ∀ wd a, (match need tbl (wdKey wd) (bad wd) with
      | .error e => (Except.error e : Except Refusal α) | .ok v => rd wd v) = .ok a → ∃ v, rd wd v = .ok a := by
    intro wd a ha
    split at ha
    · cases ha
    · exact ⟨_, ha⟩
  intro wd
  cases wd
  · exact one _ _ h1
  · exact one _ _ h2
  · exact one _ _ h3
  · exact one _ _ h4
  · exact one _ _ h5
  · exact one _ _ h6
  · exact one _ _ h7

theorem readWeekOpt_ok {α : Type} {tbl : JVal} {bad : Cal.Weekday → Refusal}
    {rd : Cal.Weekday → JVal → Except Refusal α} {f : Cal.Weekday → Option α}
    (h : readWeekOpt tbl bad rd = .ok f) : ∀ wd a, f wd = some a → ∃ v, rd wd v = .ok a := by
  unfold readWeekOpt at h
  obtain ⟨a1, h1, h⟩ := capBind_ok_elim h
  obtain ⟨a2, h2, h⟩ := capBind_ok_elim h
  obtain ⟨a3, h3, h⟩ := capBind_ok_elim h
  obtain ⟨a4, h4, h⟩ := capBind_ok_elim h
  obtain ⟨a5, h5, h⟩ := capBind_ok_elim h
  obtain ⟨a6, h6, h⟩ := capBind_ok_elim h
  obtain ⟨a7, h7, h⟩ := capBind_ok_elim h
  cases h
  have one : ∀ wd o a, (match opt tbl (wdKey wd) (bad wd) with
      | .error e => (Except.error e : Except Refusal (Option α)) | .ok none => .ok none
      | .ok (some v) => (rd wd v).map some) = .ok o → o = some a → ∃ v, rd wd v = .ok a := by
    intro wd o a ho hs
    subst hs
    split at ho
    · cases ho
    · cases ho
    · rename_i v _
      cases hr : rd wd v with
      | error e => rw [hr] at ho; cases ho
      | ok b => rw [hr] at ho; cases ho; exact ⟨v, hr⟩
  intro wd a ha
  cases wd
  · exact one _ _ _ h1 ha
  · exact one _ _ _ h2 ha
  · exact one _ _ _ h3 ha
  · exact one _ _ _ h4 ha
  · exact one _ _ _ h5 ha
  · exact one _ _ _ h6 ha
  · exact one _ _ _ h7 ha

theorem orErr_ok {α : Type} {o : Option α} {r : Refusal} {a : α} (h : orErr o r = .ok a) : o = some a := by
  unfold orErr at h
  split at h
  · cases h; rfl
  · cases h

theorem mapError_ok {ε ε' α : Type} {x : Except ε α} {f : ε → ε'} {a : α} (h : x.mapError f = .ok a) :
    x = .ok a := by
  cases x with
  | error e => cases h
  | ok b => cases h; rfl

theorem readModelTable_ok {α : Type} {t : JVal} {pm : Part} {bad : Cal.Weekday → Refusal}
    {rd : Cal.Weekday → JVal → Except Refusal α} {m : Cal.Weekday → Option α}
    (h : readModelTable t pm bad rd = .ok m) : ∀ wd a, m wd = some a → ∃ v, rd wd v = .ok a := by
  unfold readModelTable at h
  intro wd a ha
  split at h
  · cases h
  · cases h; cases ha
  · rename_i mt _
    cases hn : needObj mt pm with
    | error e => rw [hn] at h; cases h
    | ok mt' => rw [hn] at h; exact readWeekOpt_ok h wd a ha

theorem readTables_ok {α : Type} {sec : JVal} {k : String} {p pm pc : Part}
    {bad : Src → Cal.Weekday → Refusal} {rd : Src → Cal.Weekday → JVal → Except Refusal α}
    {m : Cal.Weekday → Option α} {c : Cal.Weekday → α}
    (h : readTables sec k p pm pc bad rd = .ok (m, c)) :
    (∀ wd a, m wd = some a → ∃ v, rd .model wd v = .ok a) ∧ (∀ wd, ∃ v, rd .config wd v = .ok (c wd)) := by
  unfold readTables at h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨m', hm, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨c', hc, h⟩ := capBind_ok_elim h
  cases h
  exact ⟨readModelTable_ok hm, readWeekAll_ok hc⟩

theorem readEnergyCurve_ok {loc : Loc} {v : Option JVal} {e : List (List Char × List Nat)}
    (h : readEnergyCurve loc v = .ok e) : e = [] ∨ ∃ ns, e = [(loc.curve, ns)] ∧ energyOk ns = true := by
  unfold readEnergyCurve at h
  split at h
  · cases h; exact .inl rfl
  · split at h
    · split at h
      · split at h
        · rename_i ns _ hok; cases h; exact .inr ⟨ns, rfl, hok⟩
        · cases h
      · cases h
    · cases h
  · cases h

theorem readEnergy_ok {sec : JVal} {e : List (List Char × List Nat)} (h : readEnergy sec = .ok e) :
    decide (e.map Prod.fst).Nodup = true ∧
      e.all (fun x => (x.1 == loungeKey || x.1 == homeKey) && energyOk x.2) = true := by
  unfold readEnergy at h
  split at h
  · cases h
  · cases h; simp
  · unfold readEnergyIn at h
    obtain ⟨_, -, h⟩ := capBind_ok_elim h
    obtain ⟨_, -, h⟩ := capBind_ok_elim h
    obtain ⟨l, hl, h⟩ := capBind_ok_elim h
    obtain ⟨_, -, h⟩ := capBind_ok_elim h
    obtain ⟨hh', hh, h⟩ := capBind_ok_elim h
    cases h
    rcases readEnergyCurve_ok hl with rfl | ⟨nl, rfl, hnl⟩ <;>
      rcases readEnergyCurve_ok hh with rfl | ⟨nh, rfl, hnh⟩ <;>
      simp_all [Loc.curve, loungeKey, homeKey]

theorem readCurve_ok {key : List Char} {v : JVal} {s : List Step} (h : readCurve key v = .ok s) :
    curveOk s = true := by
  unfold readCurve at h
  split at h
  · split at h
    · cases h
    · split at h
      · split at h
        · cases h; assumption
        · cases h
      · cases h
  · cases h

theorem readPrior_ok {sec : JVal} {p : List (List Char × List Step)} (h : readPrior sec = .ok p) :
    priorOk p = true := by
  unfold readPrior at h
  split at h
  · unfold readPriorObj at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h; assumption
        · cases h
  · cases h

theorem readHomeMax_ok {sec : JVal} {n : Nat} (h : readHomeMax sec = .ok n) : homeMaxOk n = true := by
  unfold readHomeMax at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

theorem mkDayCfg?_blockMin {bm br ba ml wn wd : Nat} {cap : Field.Clock} {rn rd : Nat} {c : DayCfg}
    (h : mkDayCfg? bm br ba ml wn wd cap rn rd = .ok c) : c.cut.blockMin = bm := by
  unfold mkDayCfg? at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

theorem readDay_ok {bm : Nat} {sec : JVal} {c : DayCfg} (h : readDay bm sec = .ok c) :
    c.wf = true ∧ c.cut.blockMin = bm := by
  unfold readDay at h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  have h := mapError_ok h
  exact ⟨mkDayCfg?_wf h, mkDayCfg?_blockMin h⟩

theorem readPriority_ok {sec : JVal} {b : Bins} {s : Arith.Pos} {k : Fin 4}
    (h : readPriority sec = .ok (b, s, k)) :
    (∃ xs, binsOfWire xs = some b) ∧ (∃ p, safetyOfWire p = some s) ∧ ∃ n, defaultPrioOf? n = some k := by
  unfold readPriority at h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨xs, -, h⟩ := capBind_ok_elim h
  obtain ⟨b', hb, h⟩ := capBind_ok_elim h
  obtain ⟨sp, -, h⟩ := capBind_ok_elim h
  obtain ⟨s', hs, h⟩ := capBind_ok_elim h
  obtain ⟨n, -, h⟩ := capBind_ok_elim h
  obtain ⟨k', hk, h⟩ := capBind_ok_elim h
  cases h
  exact ⟨⟨xs, orErr_ok hb⟩, ⟨sp, orErr_ok hs⟩, ⟨n, orErr_ok hk⟩⟩

/-- **What an accepted section holds**: every §13.6 bound of its own values, each weight pair sent
decoded exactly (the model's and the config's), and `[day] block_min` the request's. -/
theorem readSection_ok {bm : Nat} {cap : JVal} {s : Section} (h : readSection bm cap = .ok s) :
    Curves.wf ⟨s.prior, s.energy⟩ = true ∧ homeMaxOk s.homeMax = true ∧ s.day.wf = true ∧
      s.day.cut.blockMin = bm ∧
      (∀ wd, ∃ w, mkWeight? (s.pConfig wd).1 (s.pConfig wd).2 = .ok w) ∧
      (∀ wd p, s.pModel wd = some p → ∃ w, mkWeight? p.1 p.2 = .ok w) ∧
      (∃ xs, binsOfWire xs = some s.prio.1) ∧ (∃ p, safetyOfWire p = some s.prio.2.1) ∧
      (∃ n, defaultPrioOf? n = some s.prio.2.2) := by
  unfold readSection at h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨⟨pm, pc⟩, hp, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨en, he, h⟩ := capBind_ok_elim h
  obtain ⟨pr, hpr, h⟩ := capBind_ok_elim h
  obtain ⟨hm, hhm, h⟩ := capBind_ok_elim h
  obtain ⟨dy, hdy, h⟩ := capBind_ok_elim h
  obtain ⟨⟨b, sf, df⟩, hpo, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  cases h
  obtain ⟨hpm, hpc⟩ := readTables_ok hp
  obtain ⟨hn, ha⟩ := readEnergy_ok he
  obtain ⟨hdw, hdb⟩ := readDay_ok hdy
  obtain ⟨hb, hs, hk⟩ := readPriority_ok hpo
  refine ⟨?_, readHomeMax_ok hhm, hdw, hdb, ?_, ?_, hb, hs, hk⟩
  · simp only [Curves.wf, readPrior_ok hpr, hn, ha, Bool.and_self]
  · intro wd
    obtain ⟨v, hv⟩ := hpc wd
    exact readWeight_ok hv
  · intro wd p hpw
    obtain ⟨v, hv⟩ := hpm wd p hpw
    exact readWeight_ok hv

/-- **What an answered capacity request satisfies** (R10, §13.6): the request's `now` is today and
its `blockMin` the day's blocks and the walls' blocks; the lookahead's input is L5's `mkInput?` of
the raw input, which holds every §13.6 bound (`InputIn.boundsWf`); every weight pair sent decodes
exactly; the walls are the loaded plan's, indexed once; the zone is B1's `mkTz?`; the lookahead
ends in year 9999 at the latest; and the priority configuration went through step 2's decoders. -/
theorem readCapacity_ok {plan : PlanCore} {clock : ReqClock} {j cap : JVal} {c : CapReq}
    (h : readCapacity plan clock j cap = .ok c) :
    mkInput? c.input = .ok c.look ∧ c.input.boundsWf = true ∧
      clock.now = some c.input.today ∧ clock.blockMin.map Subtype.val = some c.input.day.cut.blockMin ∧
      c.input.walls = wallIndex c.input.tz c.input.day.cut.blockMin plan ∧
      (∀ wd, ∃ w, mkWeight? (c.input.pConfig wd).1 (c.input.pConfig wd).2 = .ok w) ∧
      (∀ wd p, c.input.pModel wd = some p → ∃ w, mkWeight? p.1 p.2 = .ok w) ∧
      lookaheadInCalendar c.input.today c.input.days = true ∧
      (∃ xs, binsOfWire xs = some c.bins) ∧ (∃ p, safetyOfWire p = some c.safety) ∧
      (∃ n, defaultPrioOf? n = some c.dflt) := by
  unfold readCapacity at h
  obtain ⟨today, htoday, h⟩ := capBind_ok_elim h
  obtain ⟨bm, hbm, h⟩ := capBind_ok_elim h
  obtain ⟨z, -, h⟩ := capBind_ok_elim h
  obtain ⟨s, hs, h⟩ := capBind_ok_elim h
  obtain ⟨I, hI, h⟩ := capBind_ok_elim h
  obtain ⟨_, hcal, h⟩ := capBind_ok_elim h
  cases h
  obtain ⟨hcw, hhm, hdw, hdb, hpc, hpm, hb, hsf, hk⟩ := readSection_ok hs
  refine ⟨mapError_ok hI, ?_, orErr_ok htoday, ?_, ?_, hpc, hpm, ?_, hb, hsf, hk⟩
  · simp only [InputIn.boundsWf, Section.input, hcw, hhm, hdw, Bool.and_self]
  · simp only [Section.input, hdb]; exact orErr_ok hbm
  · simp only [Section.input, hdb]
  · unfold inCalendar at hcal
    split at hcal
    · assumption
    · cases hcal

end CapWire

namespace CapWire

open Look

/-! ### The wire's names, as witnesses (each probed under the 8 GB cap; literals as `List Char`) -/

/-- `{"num": n, "den": d}`. -/
def pairJ (n d : JVal) : JVal := .obj [(['n', 'u', 'm'], n), (['d', 'e', 'n'], d)]

/-- The zone texts: an offset `±HH:MM:SS` (seconds kept, as a pre-1972 table has them) and a
transition `YYYY-MM-DDTHH:MM:SSZ`; anything else is refused.  Re-proved at the merge over B4's one
reader (`readTzOffset`, `readTzInstant`; gap 108), L6's ten cases unchanged. -/
theorem the_zone_texts_read_on_witnesses :
    (readTzOffset ['-', '0', '6', ':', '0', '0', ':', '0', '0']).map Subtype.val = some ⟨true, 21600⟩ ∧
    (readTzOffset ['+', '0', '5', ':', '3', '0', ':', '0', '0']).map Subtype.val = some ⟨false, 19800⟩ ∧
    (readTzOffset ['-', '0', '5', ':', '5', '0', ':', '3', '6']).map Subtype.val = some ⟨true, 21036⟩ ∧
    (readTzOffset ['-', '0', '6', ':', '0', '0']).map Subtype.val = none ∧
    (readTzOffset ['+', '2', '4', ':', '0', '0', ':', '0', '0']).map Subtype.val = none ∧
    (readTzOffset ['~', '0', '6', ':', '0', '0', ':', '0', '0']).map Subtype.val = none ∧
    readTzInstant ['2', '0', '2', '6', '-', '0', '3', '-', '0', '8', 'T', '0', '8', ':', '0', '0', ':',
      '0', '0', 'Z'] = some ⟨63908553600, 0⟩ ∧
    readTzInstant ['2', '0', '2', '6', '-', '0', '2', '-', '3', '0', 'T', '0', '8', ':', '0', '0', ':',
      '0', '0', 'Z'] = none ∧
    readTzInstant ['2', '0', '2', '6', '-', '0', '3', '-', '0', '8', 'T', '0', '8', ':', '0', '0', ':',
      '6', '0', 'Z'] = none ∧
    readTzInstant ['2', '0', '2', '6', '-', '0', '3', '-', '0', '8', 'T', '0', '8', ':', '0', '0', ':',
      '0', '0'] = none := by
  decide

/-- Chicago's 2026 table as the host sends it. -/
def chicagoTzJ (t1 t2 : List Char) : JVal :=
  .obj [(['k', 'e', 'y'], .str Cal.chicago2026.key), (['b', 'a', 's', 'e'], .str ['-', '0', '6', ':', '0', '0', ':', '0', '0']),
    (['t', 'h', 'e', 'n'], .arr [.arr [.str t1, .str ['-', '0', '5', ':', '0', '0', ':', '0', '0']],
      .arr [.str t2, .str ['-', '0', '6', ':', '0', '0', ':', '0', '0']]])]

def springJ : List Char :=
  ['2', '0', '2', '6', '-', '0', '3', '-', '0', '8', 'T', '0', '8', ':', '0', '0', ':', '0', '0', 'Z']
def fallJ : List Char :=
  ['2', '0', '2', '6', '-', '1', '1', '-', '0', '1', 'T', '0', '7', ':', '0', '0', ':', '0', '0', 'Z']

/-- **The zone table, both directions**: Chicago's two 2026 transitions read as B1's `chicago2026`;
refused by name: no `tz`, a `tz` that is not an object, no key, a base without seconds, a
transition that is not a pair, and the two transitions out of order (B1's `mkTz?`).  Re-proved at the
merge over B4's one reader (gap 108): the last two refusals are B4's `transition` and `unsorted`
(L6's `then` and `table`). -/
theorem readTz_on_witnesses :
    (readTz (.obj [(['t', 'z'], chicagoTzJ springJ fallJ)])).map Subtype.val = .ok Cal.chicago2026 ∧
    (readTz (.obj [])).map Subtype.val = .error .tzAbsent ∧
    (readTz (.obj [(['t', 'z'], .num 3)])).map Subtype.val = .error (.badTz .shape) ∧
    (readTz (.obj [(['t', 'z'], .obj [])])).map Subtype.val = .error (.badTz .key) ∧
    (readTz (.obj [(['t', 'z'], .obj [(['k', 'e', 'y'], .str []), (['b', 'a', 's', 'e'], .str ['-', '0', '6', ':', '0', '0'])])])).map
      Subtype.val = .error (.badTz .base) ∧
    (readTz (.obj [(['t', 'z'], .obj [(['k', 'e', 'y'], .str []), (['b', 'a', 's', 'e'], .str ['+', '0', '0', ':', '0', '0', ':', '0', '0']),
      (['t', 'h', 'e', 'n'], .arr [.str springJ])])])).map Subtype.val = .error (.badTz .transition) ∧
    (readTz (.obj [(['t', 'z'], chicagoTzJ fallJ springJ)])).map Subtype.val = .error (.badTz .unsorted) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **One lounge weight, both directions**: `0.9` and `1` read as their pairs; refused by name:
`10^-19` (19 places), `1.2`, a zero denominator, a numeral that is not a digit string, and 41
digits. -/
theorem readWeight_on_witnesses :
    readWeight .model .monday (pairJ (.str ['9']) (.str ['1', '0'])) = .ok (9, 10) ∧
    readWeight .config .sunday (pairJ (.str ['1']) (.str ['1'])) = .ok (1, 1) ∧
    readWeight .model .tuesday (pairJ (.str ['1'])
      (.str ['1', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']))
      = .error (.weight .weightPrecision .model .tuesday) ∧
    readWeight .config .saturday (pairJ (.str ['1', '2']) (.str ['1', '0']))
      = .error (.weight .weightAboveOne .config .saturday) ∧
    readWeight .config .friday (pairJ (.str ['9']) (.str ['0'])) = .error (.weight .badWeight .config .friday) ∧
    readWeight .config .friday (pairJ (.num 9) (.num 10)) = .error (.weight .badWeight .config .friday) ∧
    readWeight .config .friday (pairJ (.str ['-', '1']) (.str ['1', '0'])) = .error (.weight .badWeight .config .friday) ∧
    readWeight .config .friday (pairJ (.str (List.replicate 41 '0')) (.str ['1', '0']))
      = .error (.weight .badWeight .config .friday) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end CapWire

namespace CapWire

open Look

/-- A `[day]` object from its six values, keys in the wire's spelling. -/
def dayJ (br ba ml wh cap rt : JVal) : JVal :=
  .obj [(['b', 'r', 'e', 'a', 'k', 'M', 'i', 'n'], br),
    (['b', 'r', 'e', 'a', 'k', 'A', 'f', 't', 'e', 'r', 'B', 'l', 'o', 'c', 'k', 's'], ba),
    (['m', 'i', 'n', 'L', 'a', 's', 't', 'B', 'l', 'o', 'c', 'k', 'M', 'i', 'n'], ml),
    (['w', 'i', 'n', 'd', 'o', 'w', 'H', 'o', 'u', 'r', 's'], wh),
    (['w', 'i', 'n', 'd', 'o', 'w', 'C', 'a', 'p'], cap),
    (['b', 'u', 'd', 'g', 'e', 't', 'R', 'a', 't', 'i', 'o'], rt)]

/-- The shipped `[day]` on the wire: `window_hours = 8`, `window_cap = "19:00"`, `budget_ratio = 0.75`. -/
def shippedDayJ : JVal :=
  dayJ (.num 20) (.num 2) (.num 30) (pairJ (.num 8) (.num 1)) (.str ['1', '9', ':', '0', '0']) (pairJ (.num 75) (.num 100))

def inDay (d : JVal) : JVal := .obj [(['d', 'a', 'y'], d)]

/-- **`[day]`, both directions**: the shipped keys read (block length the request's 60); refused by
name, one key at a time: a zero block, a 1,441-minute break, 65 blocks between breaks, a zero last
block, 25 hours, a 24:00 cap, a ratio above one, a missing key, and no `day`. -/
theorem readDay_on_witnesses :
    (readDay 60 (inDay shippedDayJ)).map (fun c => (c.cut, c.windowHours.val, c.windowCap, c.budgetRatio.val))
      = .ok (⟨60, 20, 2, 30⟩, ⟨8, 1⟩, 1140, ⟨75, 100⟩) ∧
    (readDay 0 (inDay shippedDayJ)).map (fun _ => ()) = .error (.badDay .blockMin) ∧
    (readDay 60 (inDay (dayJ (.num 1441) (.num 2) (.num 30) (pairJ (.num 8) (.num 1)) (.str ['1', '9', ':', '0', '0'])
      (pairJ (.num 75) (.num 100))))).map (fun _ => ()) = .error (.badDay .breakMin) ∧
    (readDay 60 (inDay (dayJ (.num 20) (.num 65) (.num 30) (pairJ (.num 8) (.num 1)) (.str ['1', '9', ':', '0', '0'])
      (pairJ (.num 75) (.num 100))))).map (fun _ => ()) = .error (.badDay .breakAfterBlocks) ∧
    (readDay 60 (inDay (dayJ (.num 20) (.num 2) (.num 0) (pairJ (.num 8) (.num 1)) (.str ['1', '9', ':', '0', '0'])
      (pairJ (.num 75) (.num 100))))).map (fun _ => ()) = .error (.badDay .minLastBlockMin) ∧
    (readDay 60 (inDay (dayJ (.num 20) (.num 2) (.num 30) (pairJ (.num 25) (.num 1)) (.str ['1', '9', ':', '0', '0'])
      (pairJ (.num 75) (.num 100))))).map (fun _ => ()) = .error (.badDay .windowHours) ∧
    (readDay 60 (inDay (dayJ (.num 20) (.num 2) (.num 30) (pairJ (.num 8) (.num 1)) (.str ['2', '4', ':', '0', '0'])
      (pairJ (.num 75) (.num 100))))).map (fun _ => ()) = .error .badWindowCap ∧
    (readDay 60 (inDay (dayJ (.num 20) (.num 2) (.num 30) (pairJ (.num 8) (.num 1)) (.str ['1', '9', ':', '0', '0'])
      (pairJ (.num 101) (.num 100))))).map (fun _ => ()) = .error (.badDay .budgetRatio) ∧
    (readDay 60 (inDay (dayJ .null (.num 2) (.num 30) (pairJ (.num 8) (.num 1)) (.str ['1', '9', ':', '0', '0'])
      (pairJ (.num 75) (.num 100))))).map (fun _ => ()) = .error (.badDay .breakMin) ∧
    (readDay 60 (.obj [])).map (fun _ => ()) = .error (.badCapacity .day) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- One range on the wire; `to = null` is an open `N+` key. -/
def stepJ (a b : Nat) (to : Option Nat) (l : Nat) : JVal :=
  .obj [(['f', 'r', 'o', 'm'], pairJ (.num a) (.num b)),
    (['t', 'o'], match to with | some t => pairJ (.num t) (.num 1) | none => .null),
    (['l', 'e', 'v', 'e', 'l'], .num l)]

/-- The shipped `[energy.prior]` on the wire, home first. -/
def shippedPriorJ : JVal :=
  .obj [(homeKey, .arr [stepJ 0 1 (some 1) 3, stepJ 1 1 (some 4) 4, stepJ 4 1 (some 8) 3, stepJ 8 1 none 2]),
    (loungeKey, .arr [stepJ 0 1 (some 1) 4, stepJ 1 1 (some 5) 5, stepJ 5 1 (some 8) 4, stepJ 8 1 (some 10) 3,
      stepJ 10 1 none 2])]

def inPrior (p : JVal) : JVal := .obj [(['p', 'r', 'i', 'o', 'r'], p)]

/-- **The prior curves, both directions**: the shipped curves read as L4's `shippedPrior`; refused by
name: a key denominator above `10^6`, an empty range, an unsorted curve, a level of 6, a key twice,
a 65-character key, 17 curves, and a `prior` that is not an object. -/
theorem readPrior_on_witnesses :
    readPrior (inPrior shippedPriorJ) = .ok shippedPrior ∧
    readPrior (inPrior (.obj [(homeKey, .arr [.obj [(['f', 'r', 'o', 'm'], pairJ (.num 0) (.num 1000001)),
      (['l', 'e', 'v', 'e', 'l'], .num 3)]])])) = .error (.step .badStep homeKey) ∧
    readPrior (inPrior (.obj [(homeKey, .arr [stepJ 5 1 (some 5) 3])])) = .error (.step .badStep homeKey) ∧
    readPrior (inPrior (.obj [(homeKey, .arr [stepJ 4 1 none 3, stepJ 1 1 (some 4) 4])]))
      = .error (.step .badStep homeKey) ∧
    readPrior (inPrior (.obj [(loungeKey, .arr [stepJ 0 1 (some 1) 6])])) = .error (.step .badLevel loungeKey) ∧
    readPrior (inPrior (.obj [(homeKey, .arr []), (homeKey, .arr [])])) = .error (.badPrior homeKey) ∧
    readPrior (inPrior (.obj [(List.replicate 65 'x', .arr [])])) = .error (.badPrior (List.replicate 65 'x')) ∧
    readPrior (inPrior (.obj ((List.range 17).map (fun i => ([Char.ofNat (97 + i)], .arr [])))))
      = .error (.badPrior ['q']) ∧
    readPrior (inPrior (.arr [])) = .error (.badCapacity .prior) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def inEnergy (e : JVal) : JVal := .obj [(['e', 'n', 'e', 'r', 'g', 'y'], e)]

/-- **The learned curves, both directions**: the corpus `model.json`'s two curves read; absent is
none learned; refused by name: 11 entries, an entry of 256, an entry that is not a natural, and an
`energy` that is not an object. -/
theorem readEnergy_on_witnesses :
    readEnergy (inEnergy (.obj [(loungeKey, .arr ([4, 5, 5, 5, 5, 4, 4, 4, 3, 3, 2, 2].map JVal.num)),
      (homeKey, .arr ([3, 4, 4, 4, 3, 3, 3, 2, 2, 2, 2, 2].map JVal.num))]))
      = .ok [(loungeKey, [4, 5, 5, 5, 5, 4, 4, 4, 3, 3, 2, 2]), (homeKey, [3, 4, 4, 4, 3, 3, 3, 2, 2, 2, 2, 2])] ∧
    readEnergy (.obj []) = .ok [] ∧
    readEnergy (inEnergy (.obj [(loungeKey, .arr ((List.replicate 11 2).map JVal.num))])) = .error (.badCurve .lounge) ∧
    readEnergy (inEnergy (.obj [(homeKey, .arr ((256 :: List.replicate 11 2).map JVal.num))])) = .error (.badCurve .home) ∧
    readEnergy (inEnergy (.obj [(homeKey, .arr (.str [] :: (List.replicate 11 2).map JVal.num))])) = .error (.badCurve .home) ∧
    readEnergy (inEnergy (.num 1)) = .error (.badCapacity .energy) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A `[priority]` object from its three values. -/
def prioJ (bins safety dflt : JVal) : JVal :=
  .obj [(['p', 'r', 'i', 'o', 'r', 'i', 't', 'y'], .obj [(['b', 'i', 'n', 's'], bins), (['s', 'a', 'f', 'e', 't', 'y'], safety),
    (['d', 'e', 'f', 'a', 'u', 'l', 't', 'P', 'r', 'i', 'o', 'r', 'i', 't', 'y'], dflt)])]

def shippedBinsJ : JVal := .arr [pairJ (.num 5) (.num 10), pairJ (.num 25) (.num 100), pairJ (.num 1) (.num 10)]

/-- **`[priority]` through step 2's decoders (gap 77), both directions**: the shipped
`bins = [0.5, 0.25, 0.1]`, `safety = 1.3`, `default_priority = 3` read; refused by name: swapped
edges, a denominator above `10^18`, a zero safety, a safety above 1,000, and a default of 0 or 5. -/
theorem readPriority_on_witnesses :
    (readPriority (prioJ shippedBinsJ (pairJ (.num 13) (.num 10)) (.num 3))).map
      (fun p => (p.1.val, p.2.1.val, p.2.2)) = .ok ([⟨5, 10⟩, ⟨25, 100⟩, ⟨1, 10⟩], ⟨13, 10⟩, specDefaultPrio) ∧
    (readPriority (prioJ (.arr [pairJ (.num 1) (.num 10), pairJ (.num 1) (.num 2)]) (pairJ (.num 13) (.num 10))
      (.num 3))).map (fun _ => ()) = .error .badBins ∧
    (readPriority (prioJ (.arr [pairJ (.num 1) (.num 1000000000000000001)]) (pairJ (.num 13) (.num 10))
      (.num 3))).map (fun _ => ()) = .error .badBins ∧
    (readPriority (prioJ shippedBinsJ (pairJ (.num 0) (.num 10)) (.num 3))).map (fun _ => ()) = .error .badSafety ∧
    (readPriority (prioJ shippedBinsJ (pairJ (.num 1001) (.num 1)) (.num 3))).map (fun _ => ()) = .error .badSafety ∧
    (readPriority (prioJ shippedBinsJ (pairJ (.num 13) (.num 10)) (.num 0))).map (fun _ => ()) = .error .badDefaultPriority ∧
    (readPriority (prioJ shippedBinsJ (pairJ (.num 13) (.num 10)) (.num 5))).map (fun _ => ()) = .error .badDefaultPriority := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end CapWire

namespace CapWire

open Look

/-- A weekday table from seven values, `null` for an absent weekday. -/
def weekJ (mo tu we th fr sa su : JVal) : JVal :=
  .obj [(['M', 'o', 'n'], mo), (['T', 'u', 'e'], tu), (['W', 'e', 'd'], we), (['T', 'h', 'u'], th),
    (['F', 'r', 'i'], fr), (['S', 'a', 't'], sa), (['S', 'u', 'n'], su)]

def tenthsJ (n : Nat) : JVal := pairJ (.str (digitsOf n)) (.str ['1', '0'])
def clockJ (h1 h2 m1 m2 : Char) : JVal := .str [h1, h2, ':', m1, m2]

/-- **The corpus `model.json`, hand-shrunk, over `plan-basic/config.toml`**, as the capacity
section: the model's `p_lounge` (0.9, 0.9, 0.8, 0.9, 0.7, 0.5, 0.4) and its two learned arrivals
(Monday 07:10, Saturday 10:30), the config's tables, the learned curves, the shipped prior, `[day]`,
`home_max_ci` and `[priority]`, seven days and no logged wake. -/
def corpusSectionJ : JVal :=
  .obj [(['p', 'L', 'o', 'u', 'n', 'g', 'e'], .obj [
      (['m', 'o', 'd', 'e', 'l'], weekJ (tenthsJ 9) (tenthsJ 9) (tenthsJ 8) (tenthsJ 9) (tenthsJ 7) (tenthsJ 5) (tenthsJ 4)),
      (['c', 'o', 'n', 'f', 'i', 'g'], weekJ (tenthsJ 9) (tenthsJ 9) (tenthsJ 9) (tenthsJ 9) (tenthsJ 8) (tenthsJ 5) (tenthsJ 4))]),
    (['a', 'r', 'r', 'i', 'v', 'a', 'l'], .obj [
      (['m', 'o', 'd', 'e', 'l'], .obj [(['M', 'o', 'n'], clockJ '0' '7' '1' '0'), (['S', 'a', 't'], clockJ '1' '0' '3' '0')]),
      (['c', 'o', 'n', 'f', 'i', 'g'], weekJ (clockJ '0' '7' '0' '0') (clockJ '0' '7' '0' '0') (clockJ '0' '7' '0' '0')
        (clockJ '0' '7' '0' '0') (clockJ '0' '7' '0' '0') (clockJ '1' '0' '0' '0') (clockJ '1' '0' '0' '0'))]),
    (['e', 'n', 'e', 'r', 'g', 'y'], .obj [(loungeKey, .arr ([4, 5, 5, 5, 5, 4, 4, 4, 3, 3, 2, 2].map JVal.num)),
      (homeKey, .arr ([3, 4, 4, 4, 3, 3, 3, 2, 2, 2, 2, 2].map JVal.num))]),
    (['p', 'r', 'i', 'o', 'r'], shippedPriorJ),
    (['h', 'o', 'm', 'e', 'M', 'a', 'x', 'C', 'i'], .num 3),
    (['d', 'a', 'y'], shippedDayJ),
    (['p', 'r', 'i', 'o', 'r', 'i', 't', 'y'], .obj [(['b', 'i', 'n', 's'], shippedBinsJ),
      (['s', 'a', 'f', 'e', 't', 'y'], pairJ (.num 13) (.num 10)),
      (['d', 'e', 'f', 'a', 'u', 'l', 't', 'P', 'r', 'i', 'o', 'r', 'i', 't', 'y'], .num 3)]),
    (['d', 'a', 'y', 's'], .num 7),
    (['d', 'a', 'y', '0'], .arr ([0, 0, 0, 60, 170, 180].map JVal.num))]

def weekdays : List Cal.Weekday := [.monday, .tuesday, .wednesday, .thursday, .friday, .saturday, .sunday]

/-- **`the_capacity_section_reads_the_corpus_model`** (design §14.8's L6 row): every value of the
corpus model and config reads through its constructor, the model's weights and arrivals where it
has them, the config's beside them, and the learned curves as written. -/
theorem the_capacity_section_reads_the_corpus_model :
    (readSection 60 corpusSectionJ).map (fun s => (weekdays.map s.pModel, weekdays.map s.pConfig,
        weekdays.map s.arrModel, weekdays.map s.arrConfig, s.wake, s.energy, s.prior, s.homeMax, s.days, s.day0))
      = .ok ([some (9, 10), some (9, 10), some (8, 10), some (9, 10), some (7, 10), some (5, 10), some (4, 10)],
          [(9, 10), (9, 10), (9, 10), (9, 10), (8, 10), (5, 10), (4, 10)],
          [some 430, none, none, none, none, some 630, none],
          [420, 420, 420, 420, 420, 600, 600], none,
          [(loungeKey, [4, 5, 5, 5, 5, 4, 4, 4, 3, 3, 2, 2]), (homeKey, [3, 4, 4, 4, 3, 3, 3, 2, 2, 2, 2, 2])],
          shippedPrior, 3, 7, [0, 0, 0, 60, 170, 180]) := by
  rfl

end CapWire

namespace CapWire

open Look

/-- **The response's bytes, in build order** (design §10.2; D17's digit strings): `den`, then
`days`; a day's `day`, then `numAt`, level 0 first, every unit count a JSON string. -/
theorem the_lookahead_response_emits_in_build_order :
    jemit (unitsJson capDen) = ['"', '1', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0',
      '0', '0', '"'] ∧
    jemit (lookaheadJson []) = ['{', '"', 'd', 'e', 'n', '"', ':', '"', '1', '0', '0', '0', '0', '0', '0', '0', '0', '0',
      '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '"', 'd', 'a', 'y', 's', '"', ':', '[', ']', '}'] ∧
    jemit (dayCapJson ⟨739865, fun l => if l.val = 5 then 60 * capDen else 0⟩) =
      ['{', '"', 'd', 'a', 'y', '"', ':', '"', '2', '0', '2', '6', '-', '0', '9', '-', '0', '7', '"', ',', '"', 'n', 'u',
       'm', 'A', 't', '"', ':', '[', '"', '0', '"', ',', '"', '0', '"', ',', '"', '0', '"', ',', '"', '0', '"', ',', '"',
       '0', '"', ',', '"', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0',
       '0', '"', ']', '}'] := by
  decide

/-- The corpus section with `days` replaced. -/
def sectionWithDays (days : Nat) : JVal :=
  match corpusSectionJ with
  | .obj kvs => .obj (kvs.map fun kv => if kv.1 = ['d', 'a', 'y', 's'] then (kv.1, .num days) else kv)
  | v => v

/-- A whole request: no documents, `now` 2026-09-07 (a Monday), 60-minute blocks, Chicago's 2026
table, the corpus section. -/
def corpusRequestJ (tz : Bool) (days : Nat) : JVal :=
  .obj ([(['d', 'o', 'c', 's'], .arr []), (['n', 'o', 'w'], .str ['2', '0', '2', '6', '-', '0', '9', '-', '0', '7']),
    (['b', 'l', 'o', 'c', 'k', 'M', 'i', 'n'], .num 60)] ++
    (if tz then [(['t', 'z'], chicagoTzJ springJ fallJ)] else []) ++
    [(['c', 'a', 'p', 'a', 'c', 'i', 't', 'y'], sectionWithDays days)])

/-- **End to end at `runCap`**: the corpus request for one day answers `run`'s documents and report,
then `lookahead` with day 0 as handed in, over `capDen`; for 3,661 days it is `lookaheadTooLong`, and
without `tz` it is `tzAbsent`. -/
theorem runCap_reads_the_corpus_request :
    runCap (corpusRequestJ true 1) = .ok (jone "ok" (.obj [(['d', 'o', 'c', 's'], .arr []),
      (['r', 'e', 'p', 'o', 'r', 't'], reportJson Report.empty),
      (['l', 'o', 'o', 'k', 'a', 'h', 'e', 'a', 'd'], lookaheadJson [ofHist 739865 (histOf [0, 0, 0, 60, 170, 180])])])) ∧
    runCap (corpusRequestJ true 3661) = .error (refusalJson .lookaheadTooLong) ∧
    runCap (corpusRequestJ false 1) = .error (refusalJson .tzAbsent) := by
  refine ⟨rfl, rfl, rfl⟩

end CapWire

namespace CapWire

open Look

theorem jget_pairJ (a b : JVal) : jget (pairJ a b) "num" = .ok (some a) ∧ jget (pairJ a b) "den" = .ok (some b) :=
  ⟨rfl, rfl⟩

theorem natOfDigits_digitsOf {n : Nat} (h : n < 10 ^ 40) : natOfDigits (.str (digitsOf n)) = some n := by
  have hl : (digitsOf n).length ≤ maxDigits := digitsOf_length_le 39 n h
  simp only [natOfDigits]
  rw [if_pos hl]
  exact readNat_digitsOf n

theorem pairWith_digits {n d : Nat} (hn : n < 10 ^ 40) (hd : d < 10 ^ 40) :
    pairWith natOfDigits (pairJ (.str (digitsOf n)) (.str (digitsOf d))) = some (n, d) := by
  unfold pairWith
  rw [(jget_pairJ _ _).1, (jget_pairJ _ _).2]
  simp only [natOfDigits_digitsOf hn, natOfDigits_digitsOf hd, Option.bind_some, Option.map_some]

/-- **On the wire, a weight is read exactly when `mkWeight?` accepts it** (both directions, for the
host's digit strings): every pair in `[0, 1]` whose denominator divides `10^18` reads as itself. -/
theorem readWeight_reads_every_representable_weight (src : Src) (wd : Cal.Weekday) {n d : Nat}
    (hd : 0 < d) (hn : n ≤ d) (hp : capDen % d = 0) :
    readWeight src wd (pairJ (.str (digitsOf n)) (.str (digitsOf d))) = .ok (n, d) := by
  have hdc : d ≤ capDen := Nat.le_of_dvd capDen_pos (Nat.dvd_of_mod_eq_zero hp)
  have hc : capDen < 10 ^ 40 := by decide
  unfold readWeight
  rw [pairWith_digits (by omega) (by omega)]
  simp only [mkWeight?_accepts hd hn hp]

/-- **On the wire, more than 18 decimal places is `weightPrecision`**, whatever the digits (for
denominators the 40-digit strings can spell). -/
theorem readWeight_refuses_more_than_18_places (src : Src) (wd : Cal.Weekday) {n k : Nat} (hk : 18 < k)
    (hk40 : k < 40) (hn : n ≤ 10 ^ k) :
    readWeight src wd (pairJ (.str (digitsOf n)) (.str (digitsOf (10 ^ k))))
      = .error (.weight .weightPrecision src wd) := by
  have h10 : 10 ^ k < 10 ^ 40 := Nat.pow_lt_pow_right (by decide) hk40
  unfold readWeight
  rw [pairWith_digits (by omega) h10]
  simp only [mkWeight?_refuses_more_than_18_places hk hn]

/-- **`home_max_ci` above 5 is `badCap`**, and every level reads. -/
theorem readHomeMax_on_the_bound (n : Nat) :
    readHomeMax (.obj [(['h', 'o', 'm', 'e', 'M', 'a', 'x', 'C', 'i'], .num n)])
      = if n ≤ 5 then .ok n else .error .badCap := by
  have hj : jget (.obj [(['h', 'o', 'm', 'e', 'M', 'a', 'x', 'C', 'i'], .num n)]) "homeMaxCi" = .ok (some (.num n)) := rfl
  simp only [readHomeMax, natAt, need, hj, homeMaxOk]
  by_cases h : n ≤ 5 <;> simp [h]

/-- **More than 4,096 transitions is `badTz tooManyTransitions`**, refused before any transition is
read.  Re-proved at the merge over B4's one reader (gap 108), as an instance of B4's
`Tm.readTz_refuses_too_many_transitions`: that reader checks the key's 128-character bound first, so
the key is within it (L6's reader named the count `table` and did not bound the key). -/
theorem readTz_refuses_too_many_transitions (key base : List Char) {xs : List JVal} (h : 4096 < xs.length)
    (hb : (readTzOffset base).isSome) (hk : key.length ≤ 128) :
    readTz (.obj [(['t', 'z'], .obj [(['k', 'e', 'y'], .str key), (['b', 'a', 's', 'e'], .str base),
      (['t', 'h', 'e', 'n'], .arr xs)])]) = .error (.badTz .tooManyTransitions) := by
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hb
  have h1 : jget (.obj [(['t', 'z'], .obj [(['k', 'e', 'y'], .str key), (['b', 'a', 's', 'e'], .str base),
      (['t', 'h', 'e', 'n'], .arr xs)])]) "tz" = .ok (some (.obj [(['k', 'e', 'y'], .str key),
      (['b', 'a', 's', 'e'], .str base), (['t', 'h', 'e', 'n'], .arr xs)])) := rfl
  have h2 := Tm.readTz_refuses_too_many_transitions [(['k', 'e', 'y'], .str key), (['b', 'a', 's', 'e'], .str base),
    (['t', 'h', 'e', 'n'], .arr xs)] key base xs o rfl rfl ho rfl hk h
  simp only [readTz, h1, h2, Except.mapError]

end CapWire

/-! ## Stage 5 D10 L8 (kernel half): the grants on the wire — witnesses

APPENDED 2026-09-14 (stage 5, D10 track, step L8; design §13.6, §13.8; gaps 80, 106, 107, 109, 110).
The section's definitions sit in L6's section above, beside what they extend: `CandKey`,
`Refusal.tooManyCandidates`, `.badCandidate`, `.capacityWithCommands`, `readCapacityZ`, the candidate
readers (`readCand`, `readCands`), the grant response (`grantJson`, `lookaheadJsonWith`), and `zoneOf`,
`logSectionWith`, `runCapZ` and `runCap`; the laws follow `capBind_ok_elim`.  What stays here is the
witnesses, each probed under the 8 GB cap first. -/

namespace CapWire

open Look

/-- A candidate record on the wire: `id`, `ci`, `rootPrio`, `remaining`, `due`, `wall` and
`yesterday` given, `window`, `optional`, `overdue`, `mandatory` and `hot` false. -/
def candJ (id : List Char) (ci rp rem due wall y : JVal) : JVal :=
  .obj [(['i', 'd'], .str id), (['c', 'i'], ci), (['r', 'o', 'o', 't', 'P', 'r', 'i', 'o'], rp),
    (['r', 'e', 'm', 'a', 'i', 'n', 'i', 'n', 'g'], rem), (['d', 'u', 'e'], due),
    (['w', 'i', 'n', 'd', 'o', 'w'], .bool false), (['w', 'a', 'l', 'l'], wall),
    (['o', 'p', 't', 'i', 'o', 'n', 'a', 'l'], .bool false), (['o', 'v', 'e', 'r', 'd', 'u', 'e'], .bool false),
    (['m', 'a', 'n', 'd', 'a', 't', 'o', 'r', 'y'], .bool false), (['h', 'o', 't'], .bool false),
    (['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], y)]

/-- `capacity.candidates` around a list of records. -/
def inCands (hy : JVal) (xs : List JVal) : JVal :=
  .obj [(['c', 'a', 'n', 'd', 'i', 'd', 'a', 't', 'e', 's'],
    .obj [(['h', 'y', 's', 't', 'e', 'r', 'e', 's', 'i', 's'], hy), (['i', 't', 'e', 'm', 's'], .arr xs)])]

def sep8J : JVal := .str ['2', '0', '2', '6', '-', '0', '9', '-', '0', '8']

/-- `^a1` of `Look.witnessCands` on the wire: `ci` 3, no `!k`, 30 minutes, due 2026-09-08, yesterday 6. -/
def a1J : JVal := candJ ['a', '1'] (.num 3) .null (.num 30) sep8J (.bool false) (.num 6)

set_option maxRecDepth 8000 in
/-- **The candidates, both directions**: absent is no grants; `^a1` reads as itself; refused by name,
at its position and key: `ci` 6, `rootPrio` 5, `remaining` `2^32`, 2026-02-30, a `wall` that is not a
boolean, `yesterday` 8, a bad second record at position 1; no `hysteresis` is `badCapacity
candidates`; 1,025 records are `tooManyCandidates` before any is read. -/
theorem readCands_on_witnesses :
    readCands (.obj []) = .ok none ∧
    (readCands (inCands (.bool true) [a1J])).map (Option.map fun q => (q.hysteresis, q.cands))
      = .ok (some (true, [⟨['a', '1'], 3, none, 30, some 739866, false, false, false, false, false, false, some 6⟩])) ∧
    (readCands (inCands (.bool true) [candJ ['a'] (.num 6) .null (.num 30) sep8J (.bool false) .null])).map
      (fun _ => ()) = .error (.badCandidate 0 .ci) ∧
    (readCands (inCands (.bool true) [candJ ['a'] (.num 3) (.num 5) (.num 30) sep8J (.bool false) .null])).map
      (fun _ => ()) = .error (.badCandidate 0 .rootPrio) ∧
    (readCands (inCands (.bool true) [candJ ['a'] (.num 3) .null (.num 4294967296) sep8J (.bool false) .null])).map
      (fun _ => ()) = .error (.badCandidate 0 .remaining) ∧
    (readCands (inCands (.bool true) [candJ ['a'] (.num 3) .null (.num 30)
      (.str ['2', '0', '2', '6', '-', '0', '2', '-', '3', '0']) (.bool false) .null])).map
      (fun _ => ()) = .error (.badCandidate 0 .due) ∧
    (readCands (inCands (.bool true) [candJ ['a'] (.num 3) .null (.num 30) sep8J (.num 1) .null])).map
      (fun _ => ()) = .error (.badCandidate 0 .wall) ∧
    (readCands (inCands (.bool true) [candJ ['a'] (.num 3) .null (.num 30) sep8J (.bool false) (.num 8)])).map
      (fun _ => ()) = .error (.badCandidate 0 .yesterday) ∧
    (readCands (inCands (.bool false) [a1J, candJ ['b'] (.num 7) .null (.num 30) .null (.bool true) .null])).map
      (fun _ => ()) = .error (.badCandidate 1 .ci) ∧
    (readCands (.obj [(['c', 'a', 'n', 'd', 'i', 'd', 'a', 't', 'e', 's'], .obj [(['i', 't', 'e', 'm', 's'], .arr [])])])).map
      (fun _ => ()) = .error (.badCapacity .candidates) ∧
    (readCands (inCands (.bool true) (List.replicate 1025 .null))).map (fun _ => ()) = .error .tooManyCandidates := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The corpus request for one day with one command. -/
def corpusRequestWithACommandJ : JVal :=
  match corpusRequestJ true 1 with
  | .obj kvs => .obj (kvs ++ [(['c', 'm', 'd', 's'], .arr [.obj [(['o', 'p'], .str ['e', 's', 't']),
      (['i', 'd'], .str ['m', '1']), (['m', 'i', 'n'], .num 30)]])])
  | v => v

/-- **Gap 109's refusal, end to end**: the corpus request that `runCap_reads_the_corpus_request`
answers is refused, by name, once it also carries one command. -/
theorem runCap_refuses_a_command_beside_the_corpus_request :
    runCap corpusRequestWithACommandJ = .error (refusalJson .capacityWithCommands) := by
  rfl

/-- The wall of `Look.witnessCands`, answered: off the scale, no grant. -/
def wallOut : Look.CandOut :=
  ⟨⟨['w'], 3, none, 60, some 1, false, true, false, false, false, false, none⟩, 3, 0, none, none, .wall, none, none⟩

/-- `^a1` of `Look.witnessCands`, answered (`Look.priorities_on_a_witness`): 60 minutes available,
39 reserved, the `+0` bin, raw `p` 3 held at 5. -/
def a1Out : Look.CandOut :=
  ⟨⟨['a', '1'], 3, none, 30, some 739866, false, false, false, false, false, false, some 6⟩, 3, 39,
    some ⟨⟨39, 3, 739866⟩, 60 * capDen, 39 * capDen⟩, some (.plus 0), .pressure (.plus 0), some 3, some 5⟩

set_option maxRecDepth 8000 in
/-- **A grant's bytes, in build order** (design §13.6; stage 5 D10 L8): `id`, `class`, `k`, `p`, `rawP`,
`need`, `until`, then `avail`, `allocation` and `shortfall` as digit strings over `den` (D17), then
`bin`.  A wall has `null` for `p`, `rawP`, `until` and `bin`, and zero units; a dated candidate its
due date, its units and its bin.  Each literal is at most 85 characters (design §14.0.4). -/
theorem the_grant_response_emits_in_build_order :
    jemit (grantJson wallOut) =
      "{\"id\":\"w\",\"class\":\"wall\",\"k\":3,\"p\":null,\"rawP\":null,\"need\":0,\"until\":null,\"avail\":\"0\"".toList ++
      ",\"allocation\":\"0\",\"shortfall\":\"0\",\"bin\":null}".toList ∧
    jemit (grantJson a1Out) =
      "{\"id\":\"a1\",\"class\":\"dated\",\"k\":3,\"p\":5,\"rawP\":3,\"need\":39,\"until\":\"2026-09-08\"".toList ++
      ",\"avail\":\"60000000000000000000\",\"allocation\":\"39000000000000000000\",\"shortfall\":\"0\"".toList ++
      ",\"bin\":0}".toList := by
  constructor <;> decide

/-! ### Stage 5 D10 L8 host half: the floor on the wire (gap 79; each witness probed under the 8 GB cap first) -/

/-- A record's `floor` object on the wire. -/
def floorJ (left last : JVal) : JVal := .obj [(['l', 'e', 'f', 't'], left), (['u', 'n', 't', 'i', 'l'], last)]

/-- A candidate record with a `floor` key appended. -/
def withFloorJ (rec f : JVal) : JVal :=
  match rec with
  | .obj kvs => .obj (kvs ++ [(['f', 'l', 'o', 'o', 'r'], f)])
  | v => v

set_option maxRecDepth 8000 in
/-- **A record's floor, both directions**: `^a1` with a floor of 120 minutes to 2026-09-08 reads it; a
`null` floor is none; `left` of `2^32`, 2026-02-30 and a floor that is not an object are each
`badCandidate 0 floor`. -/
theorem readCands_reads_and_refuses_floors :
    (readCands (inCands (.bool true) [withFloorJ a1J (floorJ (.num 120) sep8J)])).map
      (Option.map fun q => q.items.map Prod.snd) = .ok (some [some ⟨120, 739866⟩]) ∧
    (readCands (inCands (.bool true) [withFloorJ a1J .null])).map
      (Option.map fun q => q.items.map Prod.snd) = .ok (some [none]) ∧
    (readCands (inCands (.bool true) [withFloorJ a1J (floorJ (.num 4294967296) sep8J)])).map
      (fun _ => ()) = .error (.badCandidate 0 .floor) ∧
    (readCands (inCands (.bool true) [withFloorJ a1J (floorJ (.num 120)
      (.str ['2', '0', '2', '6', '-', '0', '2', '-', '3', '0']))])).map
      (fun _ => ()) = .error (.badCandidate 0 .floor) ∧
    (readCands (inCands (.bool true) [withFloorJ a1J (.num 1)])).map
      (fun _ => ()) = .error (.badCandidate 0 .floor) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `^r` of `Look.witnessFloors` over `Look.witnessFloorCaps`, answered at its floor
(`Look.prioritiesWithFloors_on_a_roomier_witness`): 82 minutes left by the pass, need 26, the `+1`
bin, `p = 2`. -/
def rFloorOut : Look.FloorOut :=
  ⟨⟨⟨['r'], 2, some 0, 50, none, false, false, false, false, false, false, none⟩, 1, 26, none, some (.plus 1),
    .pressure (.plus 1), some 2, some 2⟩, some ⟨⟨20, 739866⟩, 26, 82 * capDen⟩⟩

set_option maxRecDepth 8000 in
/-- **A floor answer's bytes, in build order**: the class `floor`, `until` the floor's last date, `avail`
what the pass left, `allocation` `min(need, avail)`, then the shortfall and the bin.  Each literal is at
most 90 characters. -/
theorem the_floor_grant_response_emits_in_build_order :
    jemit (grantJsonF rFloorOut) =
      "{\"id\":\"r\",\"class\":\"floor\",\"k\":1,\"p\":2,\"rawP\":2,\"need\":26,\"until\":\"2026-09-08\"".toList ++
      ",\"avail\":\"82000000000000000000\",\"allocation\":\"26000000000000000000\",\"shortfall\":\"0\"".toList ++
      ",\"bin\":1}".toList := by
  decide

end CapWire

/-! ## Stage 5 D9 C1: the `log` op's facts — the cancelled line set

APPENDED 2026-09-14 (stage 5, D9 track, step C1; design §7.1, §10.2, §14.4 row C1).  `want.facts: true`
is accepted since C1 and answers `facts: {"cancelled": [line, …]}`, the lines of the tail's entries
that the undo mask cancels (`Replay.cancelledLines`, compiled as `Replay.cancelledLinesFast`); `facts`
is `null` otherwise, in its §10.2 place after `warnings`.  There is no checkpoint before W1–W3, so a
tail is the whole log only from line 1: facts asked of a tail from any other line are refused
`badLogReq facts` (`mkLogReq?_refuses_facts_of_a_tail_without_a_checkpoint`), never answered for
the tail alone.  The entries the mask reads are the tail's, each at its own line, so their lines
strictly increase (`the_tail_entries_have_increasing_lines`): `Replay.a_cancelled_event_is_never_revived`'s
hypothesis holds of every list the op builds. -/

section C1

theorem readLine_entry_line (n : Nat) (seg : Option (List Char)) (e : Log.Entry)
    (h : Log.readLine n seg = .entry e) : e.line = n := by
  cases seg with
  | none => simp [Log.readLine] at h
  | some l =>
    obtain ⟨kvs, -, -, ho⟩ := Log.readLine_entry_inv n l e h
    unfold Log.readObject at ho
    repeat' split at ho
    all_goals first | (cases ho; done) | (cases ho; rfl)

theorem filterMap_entryOf_lines (segs : List (Option (List Char))) : ∀ (n : Nat) (e : Log.Entry),
    e ∈ ((segs.zipIdx n).map (fun p => Log.readLine p.2 p.1)).filterMap entryOf →
      n ≤ e.line ∧ e.line < n + segs.length := by
  induction segs with
  | nil => intro n e h; simp at h
  | cons seg rest ih =>
    intro n e h
    simp only [List.zipIdx_cons, List.map_cons, List.filterMap_cons] at h
    split at h
    · have := ih (n + 1) e h; simp; omega
    · rename_i e' he'
      rcases List.mem_cons.1 h with rfl | h
      · have : Log.readLine n seg = .entry e := by
          unfold entryOf at he'; split at he' <;> simp_all
        have := readLine_entry_line n seg e this
        simp; omega
      · have := ih (n + 1) e h; simp; omega

theorem linesIncreasing_of_pairwise : ∀ (es : List Log.Entry),
    es.Pairwise (fun a b => a.line < b.line) → Log.linesIncreasing es = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    simp only [Log.linesIncreasing, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, linesIncreasing_of_pairwise _ h.of_cons⟩

theorem filterMap_entryOf_pairwise (segs : List (Option (List Char))) : ∀ (n : Nat),
    (((segs.zipIdx n).map (fun p => Log.readLine p.2 p.1)).filterMap entryOf).Pairwise
      (fun a b => a.line < b.line) := by
  induction segs with
  | nil => intro n; simp
  | cons seg rest ih =>
    intro n
    simp only [List.zipIdx_cons, List.map_cons, List.filterMap_cons]
    split
    · exact ih (n + 1)
    · rename_i e he
      have hl : e.line = n := by
        apply readLine_entry_line n seg e
        unfold entryOf at he; split at he <;> simp_all
      refine List.Pairwise.cons (fun b hb => ?_) (ih (n + 1))
      have := (filterMap_entryOf_lines rest (n + 1) b hb).1
      omega

/-- **The entries the facts are computed from have strictly increasing lines**: each is read at its
own physical line. -/
theorem the_tail_entries_have_increasing_lines (r : LogReq) :
    Log.linesIncreasing ((logVerdicts r).filterMap entryOf) = true := by
  rw [logVerdicts_eq]
  exact linesIncreasing_of_pairwise _ (filterMap_entryOf_pairwise _ _)

/-- **The `facts` key**: `null` unless asked; asked, the cancelled lines of the tail's entries. -/
theorem logAnswer_facts (r : VLogReq) :
    ∃ a b c d, logAnswer r = .obj [a, b, ("facts".toList,
      if r.val.facts then .obj [("cancelled".toList,
        .arr ((Replay.cancelledLines ((logVerdicts r.val).filterMap entryOf)).map JVal.num))] else .null), c, d] :=
  ⟨_, _, _, _, rfl⟩

/-- An accepted request asking for facts reads its tail from line 1. -/
theorem LogReq.wf_facts_from_line_one (r : LogReq) (h : r.wf = true) (hf : r.facts = true) :
    r.from_ = 1 := by
  unfold LogReq.wf LogReq.fault at h
  split at h; · simp at h
  split at h; · simp at h
  split at h; · simp at h
  split at h; · simp at h
  split at h; · simp at h
  simp only [hf, Bool.true_and] at h
  by_cases hne : r.from_ = 1
  · exact hne
  · simp [hne] at h

/-- **R10: facts of a tail without a checkpoint are refused by name** unless the tail starts at line 1
(W3's checkpoint is what will carry the lines before it).  Every earlier bound holds, so the facts are
the fault. -/
theorem mkLogReq?_refuses_facts_of_a_tail_without_a_checkpoint (r : LogReq) (h0 : 0 < r.from_)
    (h1 : r.from_ < logLineBound) (h2 : r.lines.length ≤ maxLogLines)
    (h3 : ∀ hf, r.headersFrom = some hf → hf < logLineBound) (h4 : r.render.length ≤ maxRenderLines)
    (h5 : ∀ n ∈ r.render, r.from_ ≤ n ∧ n < r.from_ + r.lines.length)
    (hf : r.facts = true) (hne : r.from_ ≠ 1) :
    mkLogReq? r = .error (.badLogReq .facts) := by
  rw [mkLogReq?_error_is_the_fault]
  have h3' : r.headersFrom.any (fun h => decide (logLineBound ≤ h)) = false := by
    cases hh : r.headersFrom with
    | none => rfl
    | some x => simp [Nat.not_le.mpr (h3 x hh)]
  have h5' : r.render.find? (fun n => n < r.from_ || r.from_ + r.lines.length ≤ n) = none := by
    apply List.find?_eq_none.2
    intro n hn
    have := h5 n hn
    simp; omega
  simp [LogReq.fault, Nat.pos_iff_ne_zero.mp h0, Nat.not_le.mpr h1, Nat.not_lt.mpr h2, h3',
    Nat.not_lt.mpr h4, h5', hf, hne]

/-- A note and the undo that cancels it, from line 1: `{"t":…,"ev":"note","text":"a"}` and
`{"t":…,"ev":"undo","of":"note"}`, 51 and 51 characters, spelled as characters (the parser reads them). -/
def factsWitnessNote : List Char :=
  ['{', '"', 't', '"', ':', '"', '2', '0', '2', '6', '-', '0', '9', '-', '0', '7', 'T', '0', '9', ':', '0', '0', ':', '0', '0', 'Z', '"', ',', '"', 'e', 'v', '"', ':', '"', 'n', 'o', 't', 'e', '"', ',', '"', 't', 'e', 'x', 't', '"', ':', '"', 'a', '"', '}']

def factsWitnessUndo : List Char :=
  ['{', '"', 't', '"', ':', '"', '2', '0', '2', '6', '-', '0', '9', '-', '0', '7', 'T', '0', '9', ':', '0', '1', ':', '0', '0', 'Z', '"', ',', '"', 'e', 'v', '"', ':', '"', 'u', 'n', 'd', 'o', '"', ',', '"', 'o', 'f', '"', ':', '"', 'n', 'o', 't', 'e', '"', '}']

set_option maxRecDepth 8000 in
/-- **The op answers the cancelled lines, end to end**: a note, the undo of it, a blank line and a
note after it, from line 1, facts asked.  Lines 1 and 2 are cancelled; line 4 survives. -/
theorem the_log_op_answers_the_cancelled_lines :
    logAnswer ⟨⟨1, [some factsWitnessNote, some factsWitnessUndo, some [], some factsWitnessNote],
        true, none, [], true⟩, by decide⟩
      = .obj [("lines".toList, .num 4), ("warnings".toList, .arr []),
          ("facts".toList, .obj [("cancelled".toList, .arr [.num 1, .num 2])]),
          ("headers".toList, .arr []), ("render".toList, .arr [])] := by
  decide

end C1
end Tm
