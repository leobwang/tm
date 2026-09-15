import TmKernel.Log
import TmKernel.Arith
/-!
# Replay — the kernel replays `.tm/log.jsonl` (stage 5, D9 track, phase C)

Design `kernel/design/stage5/stage5-D9-D10-design.md` §7 (undo), §8 (the machine and the fact
catalogue) and §14.4 (phase C).  The fork point is the in-tree Rust, `tm-core/src/log.rs`
(`undo_mask`, `DayIndex`, `Machine`, `replay_lines`); the inventory
(`kernel/design/stage5/inventory.md` §2) is the fact base.  Phase C builds this module in steps:
C1 the undo mask, C2 the day index, C3–C5 the machine's families, C6 the facts and the headers,
C7 the undo law.  **Nothing in the binary reads it yet**: the `log` op's `facts` answer (Boundary.lean)
carries what is built so far, and `tm/tests/kernel_replay_parity.rs` (T5) compares it with the Rust.

## C1: the undo mask (§7.1)

Fork `undo_mask(entries)`, over the **raw entries in file order**, before any day or range logic
(inventory §2.2).  For each `undo{of, id?}` at `i`:

* `cancelled[i] = true`: **an undo is always cancelled itself** (`an_undo_never_survives`);
* the target is the **greatest `j < i`** with `!cancelled[j]`, entry `j` not an undo,
  `ev.name() == of`, and `ev.primary_id() == Some(id)` when `id` is given; it is cancelled;
* with no target, `i` is **dangling**.

`of` is compared with the tag, so it can name any kind, `plan`, `note` or an unknown tag included:
**`is_state_change` does not restrict the mask** (`the_mask_ignores_isStateChange`).  An undo of an
undo never matches, because undos are never targets: it dangles, and there is no redo
(`an_undo_of_an_undo_cancels_nothing_in_a_canonical_log`, `a_cancelled_event_is_never_revived`).  That
law needs the log to be canonical: an `unknown` event tagged `undo`, which no reader returns, would
match, in the fork as here (`an_undo_of_an_undo_cancels_a_noncanonical_unknown_undo`).

**The specification** is a left fold over a stack of survivors, most recent first (`maskStep`):
an event is pushed, an undo removes the first (= most recent) match and never enters.  At step `i`
the stack holds exactly the entries `j < i` that are neither cancelled nor undos, most recent first,
so "the greatest uncancelled non-undo `j < i` that matches" is the stack's first match, which is
`List.eraseP`.  `survivors es` is the stack reversed, in file order.

**Positions, not entries, name a line.**  An `Entry` carries its line, but nothing in the type stops
a list from holding one entry twice, and every law here is stated for every list.  So the
cancelled set on the wire is by **position** (`stackI`, over `zipIdx`), and
`survivors_are_the_uncancelled_entries` ties it to `survivors`.  The one law that needs distinct
lines, `a_cancelled_event_is_never_revived`, takes `Log.linesIncreasing`, which the `log` op's entries
satisfy by construction (`the_tail_entries_have_increasing_lines`, Boundary.lean).

## The fast twin (`@[csimp]`, rule D9-21)

`List.eraseP` scans the stack, so a hostile log (thirty thousand events, then thirty thousand undos
of a tag or an id that is not there) costs a quadratic number of comparisons.  `maskFast` gives the
same answer from **per-tag and per-(tag, id) stacks of positions with lazy deletion**: an event's
position is pushed onto its tag's stack and, when it has a primary id, onto its `(tag, id)` stack;
an undo pops the dead positions off the top of the one stack it names, cancels the first live one,
and marks itself dead.  A position cancelled through one stack stays in the other until it reaches
the top there, where it is dropped.  Each position is pushed at most twice and dropped at most
twice, so the whole pass is linear in lookups.  The stacks live in `PosMap`, a hash table of
buckets that **replaces** a key's value (the loader's `IdMap` prepends a shadowing pair on every
insert, which is right for its insert-once uses and would grow a bucket per event here).  The
hash decides only which bucket is searched, never what is found.

`survivors_eq_survivorsFast` and `cancelledLines_eq_cancelledLinesFast` are the equalities; the
proofs stay on the specification (`maskFast_inv` is the simulation).  Both twins are `foldl`s over
the entries, so neither recurses per line.

## Rule D9-21 (functions here over a list the wire can make large)

`survivors`, `stackI`, `danglingOf` (`foldl`, specification only: compiled as their `@[csimp]` twins or
not called by the wire), `maskFast` (`foldl` of `maskFastStep`), `survivorsFast` and
`cancelledLinesFast` (`zipIdx`, `filterTR`, `mapTR`), `keyHash` (`foldl`), `pairKey`
(`flatMapTR`, `appendTR`), `PosMap.get` (`find?`), `PosMap.set` (`filterTR`), `List.dropWhile`
(a loop), and `Log.linesIncreasing` (the tail of `&&`; specification only).
-/
namespace Tm
namespace Log

/-- **The lines of a list of entries strictly increase.**  What the `log` op's entries satisfy: each
is read at its physical line (`logVerdicts_eq`), and lines only grow.  A specification: no wire
path evaluates it. -/
def linesIncreasing : List Entry → Bool
  | a :: b :: rest => decide (a.line < b.line) && linesIncreasing (b :: rest)
  | _ => true

theorem linesIncreasing_pairwise : ∀ (es : List Entry), linesIncreasing es = true →
    es.Pairwise (fun a b => a.line < b.line)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [linesIncreasing, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := linesIncreasing_pairwise (b :: rest) h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

end Log

namespace Replay

open Log (Entry Event)

/-! ## The specification (§7.1) -/

/-- **`undo{of, id}` matches `e`**: fork `ev.name() == of` and, when `id` is given,
`ev.primary_id() == Some(id)`.  The fork's `!matches!(ev, Event::Undo { .. })` is not a clause:
undos never reach the stack. -/
def «matches» (of_ : List Char) (id : Option Log.Id) (e : Entry) : Bool :=
  e.ev.tag == of_ && id.all (fun x => e.ev.primaryId == some x)

/-- The survivor stack, most recent first.  An undo removes the first (= most recent) match and never
enters. -/
def maskStep (st : List Entry) (e : Entry) : List Entry :=
  match e.ev with
  | .undo of_ id => st.eraseP («matches» of_ id)
  | _            => e :: st

/-- **The entries no undo cancelled, in file order**, undos excluded. -/
def survivors (es : List Entry) : List Entry := (es.foldl maskStep []).reverse

/-- The mask with its dangling undos: the stack, and the undos that matched nothing, most recent
first. -/
def dangleStep (acc : List Entry × List Entry) (e : Entry) : List Entry × List Entry :=
  match e.ev with
  | .undo of_ id =>
    if acc.1.any («matches» of_ id) then (acc.1.eraseP («matches» of_ id), acc.2) else (acc.1, e :: acc.2)
  | _ => (e :: acc.1, acc.2)

def danglingOf (es : List Entry) : List Entry × List Entry := es.foldl dangleStep ([], [])

/-- **`u` is an undo that matched nothing at its step** (fork `UndoMask::dangling`). -/
def dangles (es : List Entry) (u : Entry) : Bool := (danglingOf es).2.contains u

/-- The stack with each entry's position in the list (`zipIdx`): what names a line when a list holds
one entry twice. -/
def maskStepI (st : List (Entry × Nat)) (p : Entry × Nat) : List (Entry × Nat) :=
  match p.1.ev with
  | .undo of_ id => st.eraseP (fun q => «matches» of_ id q.1)
  | _            => p :: st

def stackI (es : List Entry) : List (Entry × Nat) := es.zipIdx.foldl maskStepI []

/-- **Fork `UndoMask::cancelled[i]`**: the entry at position `i` is an undo or was undone. -/
def cancelledAt (es : List Entry) (i : Nat) : Bool := !((stackI es).any (fun q => q.2 == i))

/-- **The cancelled line set**: the lines of the cancelled entries, in file order (what the `log`
op's `facts.cancelled` carries, and what T5 compares with `ViewRow::cancelled`). -/
def cancelledLines (es : List Entry) : List Nat :=
  (es.zipIdx.filter (fun p => cancelledAt es p.2)).map (fun p => p.1.line)

/-! ## The laws of the specification -/

theorem survivors_nil : survivors [] = [] := rfl

/-- `survivors_snoc_event` (Goals, §15, C1). -/
theorem survivors_snoc_event (es : List Entry) (e : Entry) (h : e.ev.isUndo = false) :
    survivors (es ++ [e]) = survivors es ++ [e] := by
  unfold survivors
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have : maskStep (es.foldl maskStep []) e = e :: es.foldl maskStep [] := by
    unfold maskStep; split
    · rename_i of_ id hev; simp [hev, Event.isUndo] at h
    · rfl
  rw [this, List.reverse_cons]

/-- `survivors_snoc_undo` (Goals, §15, C1). -/
theorem survivors_snoc_undo (es : List Entry) (e : Entry) (of_ : List Char) (id : Option Log.Id)
    (h : e.ev = .undo of_ id) :
    survivors (es ++ [e]) = ((survivors es).reverse.eraseP («matches» of_ id)).reverse := by
  unfold survivors
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.reverse_reverse]
  simp only [maskStep, h]

theorem mem_foldl_maskStep : ∀ (es : List Entry) (st : List Entry) (x : Entry),
    x ∈ es.foldl maskStep st → x ∈ st ∨ x ∈ es
  | [], _, _, h => Or.inl h
  | e :: es, st, x, h => by
    rw [List.foldl_cons] at h
    rcases mem_foldl_maskStep es _ x h with h | h
    · unfold maskStep at h
      split at h
      · exact Or.inl (List.mem_of_mem_eraseP h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr List.mem_cons_self
        · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem not_undo_of_mem_foldl_maskStep : ∀ (es : List Entry) (st : List Entry) (x : Entry),
    (∀ y ∈ st, y.ev.isUndo = false) → x ∈ es.foldl maskStep st → x.ev.isUndo = false
  | [], _, _, hst, h => hst _ h
  | e :: es, st, x, hst, h => by
    rw [List.foldl_cons] at h
    refine not_undo_of_mem_foldl_maskStep es _ x (fun y hy => ?_) h
    unfold maskStep at hy
    split at hy
    · exact hst y (List.mem_of_mem_eraseP hy)
    · rename_i hne
      rcases List.mem_cons.1 hy with rfl | hy
      · cases hev : y.ev <;> simp_all [Event.isUndo]
      · exact hst y hy

/-- **An undo never survives** (§7.1; cheat 143 is its negation's witness). -/
theorem an_undo_never_survives (es : List Entry) (u : Entry) (hu : u ∈ survivors es) :
    u.ev.isUndo = false :=
  not_undo_of_mem_foldl_maskStep es [] u (by simp) (List.mem_reverse.1 hu)

/-- A survivor is one of the log's entries. -/
theorem mem_of_mem_survivors (es : List Entry) (x : Entry) (h : x ∈ survivors es) : x ∈ es := by
  rcases mem_foldl_maskStep es [] x (List.mem_reverse.1 h) with h | h
  · simp at h
  · exact h

/-- `a_cancelled_event_is_never_revived` (Goals, §15, C1): an entry of a prefix that does not survive
it survives no extension.  `hl` is what rules out the same entry appearing again later. -/
theorem a_cancelled_event_is_never_revived (es fs : List Entry) (e : Entry)
    (hl : Log.linesIncreasing (es ++ fs) = true) (he : e ∈ es) (hc : e ∉ survivors es) :
    e ∉ survivors (es ++ fs) := by
  intro h
  have hp := List.pairwise_append.1 (Log.linesIncreasing_pairwise _ hl)
  unfold survivors at h hc
  rw [List.mem_reverse, List.foldl_append] at h
  rw [List.mem_reverse] at hc
  rcases mem_foldl_maskStep fs _ e h with h | h
  · exact hc h
  · exact Nat.lt_irrefl _ (hp.2.2 e he e h)

theorem danglingOf_fst_go : ∀ (es : List Entry) (st ds : List Entry),
    (es.foldl dangleStep (st, ds)).1 = es.foldl maskStep st
  | [], _, _ => rfl
  | e :: es, st, ds => by
    rw [List.foldl_cons, List.foldl_cons]
    have : ∃ ds', dangleStep (st, ds) e = (maskStep st e, ds') := by
      unfold dangleStep maskStep
      split
      · rename_i of_ id _
        by_cases ha : st.any («matches» of_ id) = true
        · exact ⟨ds, by simp [ha]⟩
        · refine ⟨e :: ds, ?_⟩
          simp only [ha, if_false, Bool.false_eq_true]
          rw [List.eraseP_of_forall_not]
          intro a hmem hm
          exact ha (List.any_eq_true.2 ⟨a, hmem, hm⟩)
      · exact ⟨ds, rfl⟩
    obtain ⟨ds', h⟩ := this
    rw [h]
    exact danglingOf_fst_go es _ ds'

/-- The dangling fold's stack is the mask's. -/
theorem danglingOf_fst (es : List Entry) : (danglingOf es).1 = es.foldl maskStep [] :=
  danglingOf_fst_go es [] []

theorem danglingOf_snd_mono : ∀ (fs : List Entry) (acc : List Entry × List Entry) (u : Entry),
    u ∈ acc.2 → u ∈ (fs.foldl dangleStep acc).2
  | [], _, _, h => h
  | f :: fs, acc, u, h => by
    rw [List.foldl_cons]
    apply danglingOf_snd_mono fs
    unfold dangleStep
    split
    · split
      · exact h
      · exact List.mem_cons_of_mem _ h
    · exact h

/-- `a_dangling_undo_dangles_in_every_extension` (Goals, §15, C1).  **Stated without §15's `hl` and
`hu`**, which the law does not need: the dangling undos of a prefix are dangling undos of every
extension, whatever the lines (README, C1 disagreement 2).  §15's form is this theorem applied to
fewer arguments. -/
theorem a_dangling_undo_dangles_in_every_extension (es fs : List Entry) (u : Entry)
    (hd : dangles es u = true) : dangles (es ++ fs) u = true := by
  unfold dangles danglingOf at *
  rw [List.foldl_append]
  simp only [List.contains_iff_mem] at *
  exact danglingOf_snd_mono fs _ u hd

/-- A dangling undo is an undo. -/
theorem an_entry_that_dangles_is_an_undo (es : List Entry) (u : Entry) (hd : dangles es u = true) :
    u.ev.isUndo = true := by
  unfold dangles danglingOf at hd
  simp only [List.contains_iff_mem] at hd
  suffices ∀ (fs : List Entry) (acc : List Entry × List Entry), (∀ y ∈ acc.2, y.ev.isUndo = true) →
      ∀ y ∈ (fs.foldl dangleStep acc).2, y.ev.isUndo = true from this es _ (by simp) u hd
  intro fs
  induction fs with
  | nil => intro acc h; exact h
  | cons f fs ih =>
    intro acc h
    rw [List.foldl_cons]
    apply ih
    intro y hy
    unfold dangleStep at hy
    split at hy
    · rename_i of_ id hev
      split at hy
      · exact h y hy
      · rcases List.mem_cons.1 hy with rfl | hy
        · simp [hev, Event.isUndo]
        · exact h y hy
    · exact h y hy

/-- In a canonical event (every event `readLine` returns), only an undo carries the tag `undo`: an
unknown event's tag is not a known one. -/
theorem isUndo_of_tag_undo (ev : Event) (hc : ev.canonical = true) (ht : ev.tag = Log.Kind.undo.tag) :
    ev.isUndo = true := by
  cases ev <;> try rfl
  all_goals try (simp [Event.tag, Log.Kind.tag] at ht; done)
  rename_i t rest
  simp only [Event.tag] at ht
  subst ht
  have hk : Log.isKnownTag Log.Kind.undo.tag = true := by decide
  simp [Event.canonical, hk] at hc

/-- No survivor of a canonical log matches `undo{of:"undo"}`. -/
theorem no_survivor_matches_an_undo_of_an_undo (es : List Entry) (hc : ∀ e ∈ es, e.ev.canonical = true)
    (id : Option Log.Id) (a : Entry) (ha : a ∈ es.foldl maskStep []) :
    «matches» Log.Kind.undo.tag id a = false := by
  apply Bool.eq_false_iff.2
  intro hm
  have hundo := not_undo_of_mem_foldl_maskStep es [] a (by simp) ha
  have hmem : a ∈ es := mem_of_mem_survivors es a (List.mem_reverse.2 ha)
  unfold «matches» at hm
  simp only [Bool.and_eq_true, beq_iff_eq] at hm
  rw [isUndo_of_tag_undo a.ev (hc a hmem) hm.1] at hundo
  cases hundo

/-- **An undo of an undo cancels nothing** in a canonical log: no stack entry is an undo, so
`undo{of:"undo"}` matches nothing and the survivors are unchanged (fork: no redo).  The hypothesis is
needed: an `unknown` event whose tag is `undo`, which no reader returns, would match
(`an_undo_of_an_undo_cancels_a_noncanonical_unknown_undo`). -/
theorem an_undo_of_an_undo_cancels_nothing_in_a_canonical_log (es : List Entry) (u : Entry)
    (id : Option Log.Id) (hc : ∀ e ∈ es, e.ev.canonical = true)
    (h : u.ev = .undo Log.Kind.undo.tag id) : survivors (es ++ [u]) = survivors es := by
  rw [survivors_snoc_undo es u _ id h, List.eraseP_of_forall_not, List.reverse_reverse]
  intro a ha hm
  rw [List.mem_reverse] at ha
  rw [no_survivor_matches_an_undo_of_an_undo es hc id a (by simpa [survivors] using ha)] at hm
  cases hm

theorem dangleStep_of_no_match (acc : List Entry × List Entry) (e : Entry) (of_ : List Char)
    (id : Option Log.Id) (h : e.ev = .undo of_ id) (hna : acc.1.any («matches» of_ id) = false) :
    dangleStep acc e = (acc.1, e :: acc.2) := by
  unfold dangleStep; simp [h, hna]

/-- And it dangles. -/
theorem an_undo_of_an_undo_dangles_in_a_canonical_log (es : List Entry) (u : Entry) (id : Option Log.Id)
    (hc : ∀ e ∈ es, e.ev.canonical = true)
    (h : u.ev = .undo Log.Kind.undo.tag id) : dangles (es ++ [u]) u = true := by
  unfold dangles danglingOf
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hna : (es.foldl dangleStep ([], [])).1.any («matches» Log.Kind.undo.tag id) = false := by
    rw [danglingOf_fst_go]
    apply Bool.eq_false_iff.2
    intro hany
    obtain ⟨a, ha, hm⟩ := List.any_eq_true.1 hany
    rw [no_survivor_matches_an_undo_of_an_undo es hc id a ha] at hm
    cases hm
  rw [dangleStep_of_no_match _ u _ id h hna]
  simp

/-! ## The positions: `stackI` is the stack -/

theorem maskStepI_map (st : List (Entry × Nat)) (p : Entry × Nat) :
    (maskStepI st p).map Prod.fst = maskStep (st.map Prod.fst) p.1 := by
  unfold maskStepI maskStep
  cases hev : p.1.ev <;> simp only [List.map_cons, List.eraseP_map] <;> rfl

theorem foldl_maskStepI_map : ∀ (l : List (Entry × Nat)) (st : List (Entry × Nat)),
    (l.foldl maskStepI st).map Prod.fst = (l.map Prod.fst).foldl maskStep (st.map Prod.fst)
  | [], _ => rfl
  | p :: l, st => by
    rw [List.foldl_cons, foldl_maskStepI_map l, maskStepI_map]; rfl

theorem zipIdx_map_fst (es : List Entry) (n : Nat) : (es.zipIdx n).map Prod.fst = es := by
  induction es generalizing n with
  | nil => rfl
  | cons e es ih => simp [List.zipIdx_cons, ih]

/-- `stackI` is the mask's stack, with positions. -/
theorem stackI_map (es : List Entry) : (stackI es).map Prod.fst = es.foldl maskStep [] := by
  unfold stackI
  rw [foldl_maskStepI_map, zipIdx_map_fst]; rfl

/-! ## The fast twin -/

/-- The bucket hash (the loader's `idHash` function, restated here so this module does not import
the plan). -/
def keyHash (k : List Char) : Nat := k.foldl (fun h c => (h * 31 + c.toNat) % 4294967291) 7

/-- **A table from keys to stacks of positions** whose `set` replaces the key's value in its bucket. -/
structure PosMap where
  buckets : Array (List (List Char × List Nat))

def PosMap.empty (n : Nat) : PosMap := ⟨Array.replicate (n + 1) []⟩

def PosMap.slot (m : PosMap) (k : List Char) : Nat := keyHash k % m.buckets.size

def PosMap.get (m : PosMap) (k : List Char) : List Nat :=
  match m.buckets[m.slot k]? with
  | none   => []
  | some b =>
    match b.find? (fun q => q.1 == k) with
    | some q => q.2
    | none   => []

def PosMap.set (m : PosMap) (k : List Char) (v : List Nat) : PosMap :=
  ⟨m.buckets.modify (m.slot k) (fun b => (k, v) :: b.filter (fun q => !(q.1 == k)))⟩

theorem PosMap.size_set (m : PosMap) (k : List Char) (v : List Nat) :
    (m.set k v).buckets.size = m.buckets.size := by simp [PosMap.set]

theorem PosMap.get_empty (n : Nat) (k : List Char) : (PosMap.empty n).get k = [] := by
  simp only [PosMap.get, PosMap.slot, PosMap.empty, Array.getElem?_replicate, Array.size_replicate]
  split
  · rfl
  · rename_i b hb
    split at hb
    · cases hb; rfl
    · cases hb

theorem find?_filter_ne (b : List (List Char × List Nat)) (k j : List Char) (h : j ≠ k) :
    (b.filter (fun q => !(q.1 == k))).find? (fun q => q.1 == j) = b.find? (fun q => q.1 == j) := by
  induction b with
  | nil => rfl
  | cons q b ih =>
    by_cases hq : q.1 = k
    · have h1 : (!(q.1 == k)) = false := by simp [hq]
      have h2 : (q.1 == j) = false := by rw [hq]; exact beq_false_of_ne (Ne.symm h)
      rw [List.filter_cons, if_neg (by simp [h1]), ih, List.find?_cons, h2]
    · have h1 : (!(q.1 == k)) = true := by simp [hq]
      rw [List.filter_cons, if_pos h1, List.find?_cons, List.find?_cons, ih]

theorem PosMap.get_set (m : PosMap) (k j : List Char) (v : List Nat) (hpos : 0 < m.buckets.size) :
    (m.set k v).get j = if j = k then v else m.get j := by
  have hlt : ∀ x, keyHash x % m.buckets.size < m.buckets.size := fun x => Nat.mod_lt _ hpos
  unfold PosMap.get
  simp only [PosMap.slot, PosMap.size_set]
  simp only [PosMap.set, PosMap.slot, Array.getElem?_modify, Array.getElem?_eq_getElem (hlt j)]
  by_cases hjk : j = k
  · subst hjk; simp
  · by_cases hs : keyHash k % m.buckets.size = keyHash j % m.buckets.size
    · have hb : (k == j) = false := beq_false_of_ne (Ne.symm hjk)
      simp only [hs, if_true, Option.map_some, List.find?_cons, hb, hjk, if_false]
      rw [find?_filter_ne _ _ _ hjk]
    · simp [hs, hjk]

/-- Positions pushed per tag, and per tag and id: the key of a `(tag, id)` stack.  Injective
(`pairKey_inj`): each character of the tag is prefixed by `1`, and `0` ends the tag. -/
def pairKey (tag id : List Char) : List Char := tag.flatMap (fun c => ['1', c]) ++ '0' :: id

theorem pairKey_inj : ∀ (a b x y : List Char), pairKey a x = pairKey b y → a = b ∧ x = y
  | [], [], x, y, h => by simpa [pairKey] using h
  | [], c :: _, _, _, h => by simp [pairKey] at h
  | c :: _, [], _, _, h => by simp [pairKey] at h
  | c :: a, d :: b, x, y, h => by
    simp only [pairKey, List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq,
      true_and] at h
    obtain ⟨hcd, h⟩ := h
    have := pairKey_inj a b x y h
    exact ⟨by rw [hcd, this.1], this.2⟩

/-- Whether position `j` has been marked dead (cancelled, or an undo). -/
def deadAt (dead : Array Bool) (j : Nat) : Bool := dead[j]?.getD false

structure MaskState where
  dead  : Array Bool
  byTag : PosMap
  byKey : PosMap

/-- **One entry of the fast pass.**  The state is taken apart in the pattern, and every lookup is
done before the update, so each table and the array reach their update with no other reference and
are changed in place (the loader's `dedupStep` pattern). -/
def maskFastStep : MaskState → Entry × Nat → MaskState
  | ⟨dead, byTag, byKey⟩, (e, k) =>
    match e.ev with
    | .undo of_ none =>
      match (byTag.get of_).dropWhile (deadAt dead) with
      | []        => ⟨dead.setIfInBounds k true, byTag.set of_ [], byKey⟩
      | j :: rest => ⟨(dead.setIfInBounds j true).setIfInBounds k true, byTag.set of_ rest, byKey⟩
    | .undo of_ (some x) =>
      match (byKey.get (pairKey of_ x)).dropWhile (deadAt dead) with
      | []        => ⟨dead.setIfInBounds k true, byTag, byKey.set (pairKey of_ x) []⟩
      | j :: rest => ⟨(dead.setIfInBounds j true).setIfInBounds k true, byTag, byKey.set (pairKey of_ x) rest⟩
    | _ =>
      match e.ev.primaryId with
      | none   => ⟨dead, byTag.set e.ev.tag (k :: byTag.get e.ev.tag), byKey⟩
      | some x =>
        ⟨dead, byTag.set e.ev.tag (k :: byTag.get e.ev.tag),
          byKey.set (pairKey e.ev.tag x) (k :: byKey.get (pairKey e.ev.tag x))⟩

def MaskState.init (n : Nat) : MaskState :=
  ⟨Array.replicate n false, PosMap.empty n, PosMap.empty n⟩

/-- **The dead positions**, by the fast pass. -/
def maskFast (es : List Entry) : Array Bool :=
  (es.zipIdx.foldl maskFastStep (MaskState.init es.length)).dead

def survivorsFast (es : List Entry) : List Entry :=
  let d := maskFast es
  (es.zipIdx.filter (fun p => !deadAt d p.2)).map Prod.fst

def cancelledLinesFast (es : List Entry) : List Nat :=
  let d := maskFast es
  (es.zipIdx.filter (fun p => deadAt d p.2)).map (fun p => p.1.line)

/-! ### The simulation -/

theorem deadAt_set (d : Array Bool) (i j : Nat) (h : i < d.size) :
    deadAt (d.setIfInBounds i true) j = (j == i || deadAt d j) := by
  unfold deadAt
  by_cases hij : i = j
  · subst hij; simp [Array.getElem?_setIfInBounds_self_of_lt h]
  · rw [Array.getElem?_setIfInBounds_ne hij]
    have : (j == i) = false := beq_false_of_ne (Ne.symm hij)
    simp [this]

theorem filter_dropWhile_cons (dd : Nat → Bool) : ∀ (L rest : List Nat) (j : Nat),
    L.dropWhile dd = j :: rest →
    L.filter (fun x => !dd x) = j :: rest.filter (fun x => !dd x) ∧ rest.Sublist L ∧ j ∈ L
  | [], _, _, h => by simp at h
  | a :: L, rest, j, h => by
    rw [List.dropWhile_cons] at h
    by_cases ha : dd a = true
    · rw [if_pos ha] at h
      obtain ⟨h1, h2, h3⟩ := filter_dropWhile_cons dd L rest j h
      refine ⟨?_, h2.cons a, List.mem_cons_of_mem _ h3⟩
      simp [ha, h1]
    · rw [if_neg ha] at h
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [ha]

theorem filter_dropWhile_nil (dd : Nat → Bool) : ∀ (L : List Nat),
    L.dropWhile dd = [] → L.filter (fun x => !dd x) = []
  | [], _ => rfl
  | a :: L, h => by
    rw [List.dropWhile_cons] at h
    by_cases ha : dd a = true
    · rw [if_pos ha] at h; simp [ha, filter_dropWhile_nil dd L h]
    · rw [if_neg ha] at h; cases h

/-- **`eraseP` is a filter by position** when positions are distinct and the first match is at `j`. -/
theorem eraseP_eq_filter_pos (pr : Entry → Bool) : ∀ (st : List (Entry × Nat)) (j : Nat) (t : List Nat),
    (st.map Prod.snd).Nodup → (st.filter (fun q => pr q.1)).map Prod.snd = j :: t →
    st.eraseP (fun q => pr q.1) = st.filter (fun q => q.2 != j)
  | [], _, _, _, h => by simp at h
  | q :: st, j, t, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases hq : pr q.1 = true
    · rw [List.filter_cons, if_pos hq, List.map_cons, List.cons.injEq] at h
      rw [List.eraseP_cons, hq, cond_true, List.filter_cons]
      have hqj : (q.2 != j) = false := by simp [h.1]
      rw [hqj, if_neg (by simp)]
      symm; rw [List.filter_eq_self]
      intro a ha
      have : a.2 ≠ j := by
        intro hc; rw [← h.1] at hc
        exact hnd.1 (hc ▸ List.mem_map_of_mem ha)
      simpa using this
    · rw [List.filter_cons, if_neg hq] at h
      rw [List.eraseP_cons]
      simp only [hq, cond_false]
      have hjmem : j ∈ st.map Prod.snd := by
        have : j ∈ (st.filter (fun q => pr q.1)).map Prod.snd := by rw [h]; exact List.mem_cons_self
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 this
        exact List.mem_map_of_mem (List.mem_filter.1 ha).1
      have hqj : (q.2 != j) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro hc; exact hnd.1 (hc ▸ hjmem)
      rw [List.filter_cons, if_pos hqj, eraseP_eq_filter_pos pr st j t hnd.2 h]

theorem eraseP_eq_self_of_filter_nil (pr : Entry → Bool) (st : List (Entry × Nat))
    (h : st.filter (fun q => pr q.1) = []) : st.eraseP (fun q => pr q.1) = st := by
  apply List.eraseP_of_forall_not
  intro a ha hp
  have : a ∈ st.filter (fun q => pr q.1) := List.mem_filter.2 ⟨ha, hp⟩
  rw [h] at this; cases this

/-- **The simulation invariant** after processing `P` (positions below `b`): the stack in file order is
`P`'s live entries; each tag's and each `(tag, id)`'s stack, dead positions removed, is the stack's
matching positions; every stored position is below `b`, and nothing at or above `b` is dead. -/
structure Inv (P : List (Entry × Nat)) (b : Nat) (s : MaskState) : Prop where
  stack : (P.foldl maskStepI []).reverse = P.filter (fun p => !deadAt s.dead p.2)
  tag   : ∀ g, (s.byTag.get g).filter (fun j => !deadAt s.dead j)
            = ((P.foldl maskStepI []).filter (fun q => «matches» g none q.1)).map Prod.snd
  key   : ∀ g x, (s.byKey.get (pairKey g x)).filter (fun j => !deadAt s.dead j)
            = ((P.foldl maskStepI []).filter (fun q => «matches» g (some x) q.1)).map Prod.snd
  tagLt : ∀ g, ∀ j ∈ s.byTag.get g, j < b
  keyLt : ∀ k, ∀ j ∈ s.byKey.get k, j < b
  above : ∀ j, b ≤ j → deadAt s.dead j = false
  posLt : ∀ p ∈ P, p.2 < b
  incr  : (P.map Prod.snd).Pairwise (· < ·)
  tagPos : 0 < s.byTag.buckets.size
  keyPos : 0 < s.byKey.buckets.size

theorem Inv.nodup {P : List (Entry × Nat)} {b : Nat} {s : MaskState} (h : Inv P b s) :
    ((P.foldl maskStepI []).map Prod.snd).Nodup := by
  have h1 : ((P.foldl maskStepI []).reverse.map Prod.snd).Pairwise (· < ·) := by
    rw [h.stack]
    exact h.incr.sublist (List.filter_sublist.map Prod.snd)
  rw [List.map_reverse, List.pairwise_reverse] at h1
  exact h1.imp (fun hab => Nat.ne_of_gt hab)

/-- Killing `j` and `k` (both at or above nothing stored except `j`) filters `j` out of any list of
positions below `b ≤ k`. -/
theorem filter_kill (d : Array Bool) (j k b : Nat) (hj : j < d.size) (hk : k < d.size)
    (L : List Nat) (hL : ∀ x ∈ L, x < b) (hb : b ≤ k) :
    L.filter (fun x => !deadAt ((d.setIfInBounds j true).setIfInBounds k true) x)
      = (L.filter (fun x => !deadAt d x)).filter (fun x => x != j) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x hx
  have hxk : (x == k) = false := beq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le (hL x hx) hb))
  rw [deadAt_set _ _ _ (by simpa using hk), deadAt_set _ _ _ hj, hxk]
  cases deadAt d x <;> cases hxj : (x == j) <;> simp_all

theorem filter_kill1 (d : Array Bool) (k b : Nat) (hk : k < d.size)
    (L : List Nat) (hL : ∀ x ∈ L, x < b) (hb : b ≤ k) :
    L.filter (fun x => !deadAt (d.setIfInBounds k true) x) = L.filter (fun x => !deadAt d x) := by
  apply List.filter_congr
  intro x hx
  have hxk : (x == k) = false := beq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le (hL x hx) hb))
  rw [deadAt_set _ _ _ hk, hxk]; rfl

theorem filter_pos_ne_comm (st : List (Entry × Nat)) (f : Entry × Nat → Bool) (j : Nat) :
    ((st.filter (fun q => q.2 != j)).filter f).map Prod.snd
      = ((st.filter f).map Prod.snd).filter (fun x => x != j) := by
  induction st with
  | nil => rfl
  | cons q st ih =>
    by_cases h1 : (q.2 != j) = true <;> by_cases h2 : f q = true <;>
      simp_all

theorem foldl_snoc_maskStepI (P : List (Entry × Nat)) (p : Entry × Nat) :
    (P ++ [p]).foldl maskStepI [] = maskStepI (P.foldl maskStepI []) p := by
  rw [List.foldl_append]; rfl

/-- Positions below `b` of the stack and of `P` are unaffected by dead marks at `k ≥ b`. -/
theorem stack_positions_lt {P : List (Entry × Nat)} {b : Nat} {s : MaskState} (h : Inv P b s) :
    ∀ q ∈ P.foldl maskStepI [], q.2 < b := by
  intro q hq
  have : q ∈ (P.foldl maskStepI []).reverse := List.mem_reverse.2 hq
  rw [h.stack] at this
  exact h.posLt q ((List.mem_filter.1 this).1)

theorem Inv.step_undo_none {P : List (Entry × Nat)} {b : Nat} {s : MaskState} (h : Inv P b s)
    (e : Entry) (k : Nat) (of_ : List Char) (hev : e.ev = .undo of_ none) (hb : b ≤ k)
    (hk : k < s.dead.size) :
    Inv (P ++ [(e, k)]) (k + 1) (maskFastStep s (e, k)) ∧
      (maskFastStep s (e, k)).dead.size = s.dead.size := by
  obtain ⟨dead, byTag, byKey⟩ := s
  have hstep : maskStepI (P.foldl maskStepI []) (e, k)
      = (P.foldl maskStepI []).eraseP (fun q => «matches» of_ none q.1) := by
    simp only [maskStepI, hev]
  have hlast : ∀ d : Array Bool, deadAt d k = true → (P ++ [(e, k)]).filter (fun p => !deadAt d p.2)
      = P.filter (fun p => !deadAt d p.2) := by
    intro d hd; simp [List.filter_append, hd]
  simp only [maskFastStep, hev]
  split
  · rename_i hdrop
    have hnil := filter_dropWhile_nil (deadAt dead) _ hdrop
    have hst : (P.foldl maskStepI []).filter (fun q => «matches» of_ none q.1) = [] := by
      have := h.tag of_; simp only at this; rw [hnil] at this
      exact List.map_eq_nil_iff.1 this.symm
    have herase := eraseP_eq_self_of_filter_nil _ _ hst
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp⟩
    · simp only
      rw [foldl_snoc_maskStepI, hstep, herase, hlast _ (by rw [deadAt_set _ _ _ hk]; simp), h.stack]
      symm; apply List.filter_congr; intro p hp
      rw [deadAt_set _ _ _ hk]
      have : (p.2 == k) = false := beq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le (h.posLt p hp) hb))
      rw [this]; rfl
    · intro g; simp only
      rw [PosMap.get_set _ _ _ _ h.tagPos, foldl_snoc_maskStepI, hstep, herase]
      by_cases hg : g = of_
      · subst hg; rw [if_pos rfl, hst]; rfl
      · rw [if_neg hg, filter_kill1 _ _ b hk _ (h.tagLt g) hb]; exact h.tag g
    · intro g x; simp only
      rw [foldl_snoc_maskStepI, hstep, herase, filter_kill1 _ _ b hk _ (h.keyLt _) hb]
      exact h.key g x
    · intro g j hj; simp only at hj
      rw [PosMap.get_set _ _ _ _ h.tagPos] at hj
      split at hj
      · cases hj
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.tagLt g j hj) hb)
    · intro g j hj; exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.keyLt g j hj) hb)
    · intro j hj; simp only
      rw [deadAt_set _ _ _ hk]
      have : (j == k) = false := beq_false_of_ne (by omega)
      rw [this, h.above j (by omega)]; rfl
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.posLt p hp) hb)
      · simp at hp; subst hp; exact Nat.lt_succ_self _
    · rw [List.map_append, List.pairwise_append]
      refine ⟨h.incr, List.pairwise_singleton _ _, ?_⟩
      intro a ha c hc
      simp at hc; subst hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      exact Nat.lt_of_lt_of_le (h.posLt p hp) hb
    · simp only; rw [PosMap.size_set]; exact h.tagPos
    · exact h.keyPos
  · rename_i j rest hdrop
    obtain ⟨hfl, hsub, hjmem⟩ := filter_dropWhile_cons (deadAt dead) _ rest j hdrop
    have hjb : j < b := h.tagLt of_ j hjmem
    -- `j` is below `b ≤ k < size`
    have hjd : j < dead.size := Nat.lt_of_lt_of_le hjb (Nat.le_of_lt (Nat.lt_of_le_of_lt hb hk))
    have htag := h.tag of_
    simp only at htag
    rw [hfl] at htag
    have herase := eraseP_eq_filter_pos (fun e => «matches» of_ none e) _ j _ h.nodup htag.symm
    have hk' : k < (dead.setIfInBounds j true).size := by simpa using hk
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp⟩
    · simp only
      rw [foldl_snoc_maskStepI, hstep, herase, ← List.filter_reverse, h.stack, hlast _ (by rw [deadAt_set _ _ _ hk']; simp), List.filter_filter]
      apply List.filter_congr; intro p hp
      rw [deadAt_set _ _ _ hk', deadAt_set _ _ _ hjd]
      have : (p.2 == k) = false :=
        beq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le (h.posLt p hp) hb))
      rw [this]
      cases deadAt dead p.2 <;> cases hpj : (p.2 == j) <;> simp_all
    · intro g; simp only
      rw [PosMap.get_set _ _ _ _ h.tagPos, foldl_snoc_maskStepI, hstep, herase, filter_pos_ne_comm]
      by_cases hg : g = of_
      · subst hg
        rw [if_pos rfl, filter_kill _ _ _ b hjd hk _ (fun x hx => h.tagLt g x (hsub.subset hx)) hb, ← htag]
        simp
      · rw [if_neg hg, filter_kill _ _ _ b hjd hk _ (h.tagLt g) hb, h.tag g]
    · intro g x; simp only
      rw [foldl_snoc_maskStepI, hstep, herase, filter_pos_ne_comm,
        filter_kill _ _ _ b hjd hk _ (h.keyLt _) hb, h.key g x]
    · intro g i hi; simp only at hi
      rw [PosMap.get_set _ _ _ _ h.tagPos] at hi
      split at hi
      · rename_i hg; subst hg
        exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.tagLt _ i (hsub.subset hi)) hb)
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.tagLt g i hi) hb)
    · intro g i hi; exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.keyLt g i hi) hb)
    · intro i hi; simp only
      rw [deadAt_set _ _ _ hk', deadAt_set _ _ _ hjd]
      have h1 : (i == k) = false := beq_false_of_ne (by omega)
      have h2 : (i == j) = false := beq_false_of_ne (by omega)
      rw [h1, h2, h.above i (by omega)]; rfl
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.posLt p hp) hb)
      · simp at hp; subst hp; exact Nat.lt_succ_self _
    · rw [List.map_append, List.pairwise_append]
      refine ⟨h.incr, List.pairwise_singleton _ _, ?_⟩
      intro a ha c hc
      simp at hc; subst hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      exact Nat.lt_of_lt_of_le (h.posLt p hp) hb
    · simp only; rw [PosMap.size_set]; exact h.tagPos
    · exact h.keyPos

theorem Inv.posLt_snoc {P : List (Entry × Nat)} {b : Nat} {s : MaskState} (h : Inv P b s)
    (e : Entry) (k : Nat) (hb : b ≤ k) : ∀ p ∈ P ++ [(e, k)], p.2 < k + 1 := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.posLt p hp) hb)
  · simp at hp; subst hp; exact Nat.lt_succ_self _

theorem Inv.incr_snoc {P : List (Entry × Nat)} {b : Nat} {s : MaskState} (h : Inv P b s)
    (e : Entry) (k : Nat) (hb : b ≤ k) : ((P ++ [(e, k)]).map Prod.snd).Pairwise (· < ·) := by
  rw [List.map_append, List.pairwise_append]
  refine ⟨h.incr, List.pairwise_singleton _ _, ?_⟩
  intro a ha c hc
  simp at hc; subst hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
  exact Nat.lt_of_lt_of_le (h.posLt p hp) hb

theorem Inv.step_undo_some {P : List (Entry × Nat)} {b : Nat} {s : MaskState} (h : Inv P b s)
    (e : Entry) (k : Nat) (of_ x : List Char) (hev : e.ev = .undo of_ (some x)) (hb : b ≤ k)
    (hk : k < s.dead.size) :
    Inv (P ++ [(e, k)]) (k + 1) (maskFastStep s (e, k)) ∧
      (maskFastStep s (e, k)).dead.size = s.dead.size := by
  obtain ⟨dead, byTag, byKey⟩ := s
  have hstep : maskStepI (P.foldl maskStepI []) (e, k)
      = (P.foldl maskStepI []).eraseP (fun q => «matches» of_ (some x) q.1) := by
    simp only [maskStepI, hev]
  have hlast : ∀ d : Array Bool, deadAt d k = true → (P ++ [(e, k)]).filter (fun p => !deadAt d p.2)
      = P.filter (fun p => !deadAt d p.2) := by
    intro d hd; simp [List.filter_append, hd]
  simp only [maskFastStep, hev]
  split
  · rename_i hdrop
    have hnil := filter_dropWhile_nil (deadAt dead) _ hdrop
    have hst : (P.foldl maskStepI []).filter (fun q => «matches» of_ (some x) q.1) = [] := by
      have := h.key of_ x; simp only at this; rw [hnil] at this
      exact List.map_eq_nil_iff.1 this.symm
    have herase := eraseP_eq_self_of_filter_nil _ _ hst
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, h.posLt_snoc e k hb, h.incr_snoc e k hb, h.tagPos, ?_⟩, by simp⟩
    · simp only
      rw [foldl_snoc_maskStepI, hstep, herase, hlast _ (by rw [deadAt_set _ _ _ hk]; simp), h.stack]
      symm; apply List.filter_congr; intro p hp
      rw [deadAt_set _ _ _ hk]
      have : (p.2 == k) = false := beq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le (h.posLt p hp) hb))
      rw [this]; rfl
    · intro g; simp only
      rw [foldl_snoc_maskStepI, hstep, herase, filter_kill1 _ _ b hk _ (h.tagLt g) hb]
      exact h.tag g
    · intro g y; simp only
      rw [PosMap.get_set _ _ _ _ h.keyPos, foldl_snoc_maskStepI, hstep, herase]
      by_cases hgy : pairKey g y = pairKey of_ x
      · obtain ⟨rfl, rfl⟩ := pairKey_inj _ _ _ _ hgy
        rw [if_pos rfl, hst]; rfl
      · rw [if_neg hgy, filter_kill1 _ _ b hk _ (h.keyLt _) hb]; exact h.key g y
    · intro g j hj; exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.tagLt g j hj) hb)
    · intro g j hj; simp only at hj
      rw [PosMap.get_set _ _ _ _ h.keyPos] at hj
      split at hj
      · cases hj
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.keyLt g j hj) hb)
    · intro j hj; simp only
      rw [deadAt_set _ _ _ hk]
      have : (j == k) = false := beq_false_of_ne (by omega)
      rw [this, h.above j (by omega)]; rfl
    · simp only; rw [PosMap.size_set]; exact h.keyPos
  · rename_i j rest hdrop
    obtain ⟨hfl, hsub, hjmem⟩ := filter_dropWhile_cons (deadAt dead) _ rest j hdrop
    have hjb : j < b := h.keyLt _ j hjmem
    have hjd : j < dead.size := Nat.lt_of_lt_of_le hjb (Nat.le_of_lt (Nat.lt_of_le_of_lt hb hk))
    have hkey := h.key of_ x
    simp only at hkey
    rw [hfl] at hkey
    have herase := eraseP_eq_filter_pos (fun e => «matches» of_ (some x) e) _ j _ h.nodup hkey.symm
    have hk' : k < (dead.setIfInBounds j true).size := by simpa using hk
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, h.posLt_snoc e k hb, h.incr_snoc e k hb, h.tagPos, ?_⟩, by simp⟩
    · simp only
      rw [foldl_snoc_maskStepI, hstep, herase, ← List.filter_reverse, h.stack,
        hlast _ (by rw [deadAt_set _ _ _ hk']; simp), List.filter_filter]
      apply List.filter_congr; intro p hp
      rw [deadAt_set _ _ _ hk', deadAt_set _ _ _ hjd]
      have : (p.2 == k) = false :=
        beq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le (h.posLt p hp) hb))
      rw [this]
      cases deadAt dead p.2 <;> cases hpj : (p.2 == j) <;> simp_all
    · intro g; simp only
      rw [foldl_snoc_maskStepI, hstep, herase, filter_pos_ne_comm,
        filter_kill _ _ _ b hjd hk _ (h.tagLt g) hb, h.tag g]
    · intro g y; simp only
      rw [PosMap.get_set _ _ _ _ h.keyPos, foldl_snoc_maskStepI, hstep, herase, filter_pos_ne_comm]
      by_cases hgy : pairKey g y = pairKey of_ x
      · obtain ⟨rfl, rfl⟩ := pairKey_inj _ _ _ _ hgy
        rw [if_pos rfl, filter_kill _ _ _ b hjd hk _ (fun i hi => h.keyLt _ i (hsub.subset hi)) hb, ← hkey]
        simp
      · rw [if_neg hgy, filter_kill _ _ _ b hjd hk _ (h.keyLt _) hb, h.key g y]
    · intro g i hi; exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.tagLt g i hi) hb)
    · intro g i hi; simp only at hi
      rw [PosMap.get_set _ _ _ _ h.keyPos] at hi
      split at hi
      · rename_i hg; subst hg
        exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.keyLt _ i (hsub.subset hi)) hb)
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.keyLt g i hi) hb)
    · intro i hi; simp only
      rw [deadAt_set _ _ _ hk', deadAt_set _ _ _ hjd]
      have h1 : (i == k) = false := beq_false_of_ne (by omega)
      have h2 : (i == j) = false := beq_false_of_ne (by omega)
      rw [h1, h2, h.above i (by omega)]; rfl
    · simp only; rw [PosMap.size_set]; exact h.keyPos

theorem maskFastStep_event (dead : Array Bool) (byTag byKey : PosMap) (e : Entry) (k : Nat)
    (hev : e.ev.isUndo = false) :
    maskFastStep ⟨dead, byTag, byKey⟩ (e, k) =
      ⟨dead, byTag.set e.ev.tag (k :: byTag.get e.ev.tag),
        match e.ev.primaryId with
        | none   => byKey
        | some x => byKey.set (pairKey e.ev.tag x) (k :: byKey.get (pairKey e.ev.tag x))⟩ := by
  simp only [maskFastStep]
  split
  · rename_i of_ hq; simp [hq, Event.isUndo] at hev
  · rename_i of_ x hq; simp [hq, Event.isUndo] at hev
  · cases e.ev.primaryId <;> rfl

theorem maskStepI_event (st : List (Entry × Nat)) (p : Entry × Nat) (hev : p.1.ev.isUndo = false) :
    maskStepI st p = p :: st := by
  unfold maskStepI
  split
  · rename_i of_ id hq; simp [hq, Event.isUndo] at hev
  · rfl

theorem Inv.step_event {P : List (Entry × Nat)} {b : Nat} {s : MaskState} (h : Inv P b s)
    (e : Entry) (k : Nat) (hev : e.ev.isUndo = false) (hb : b ≤ k) :
    Inv (P ++ [(e, k)]) (k + 1) (maskFastStep s (e, k)) ∧
      (maskFastStep s (e, k)).dead.size = s.dead.size := by
  obtain ⟨dead, byTag, byKey⟩ := s
  have hst : (P ++ [(e, k)]).foldl maskStepI [] = (e, k) :: P.foldl maskStepI [] := by
    rw [foldl_snoc_maskStepI, maskStepI_event _ _ hev]
  have hka : deadAt dead k = false := h.above k hb
  rw [maskFastStep_event _ _ _ _ _ hev]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, h.posLt_snoc e k hb, h.incr_snoc e k hb, ?_, ?_⟩, rfl⟩
  · simp only
    rw [hst, List.reverse_cons, h.stack, List.filter_append]
    simp [hka]
  · intro g; simp only
    rw [PosMap.get_set _ _ _ _ h.tagPos, hst, List.filter_cons]
    by_cases hg : g = e.ev.tag
    · have hm : «matches» g none e = true := by simp [«matches», hg]
      rw [if_pos hg, if_pos hm, List.filter_cons, if_pos (by simp [hka]), List.map_cons]
      rw [hg]; exact congrArg _ (hg ▸ h.tag g)
    · have hm : «matches» g none e = false := by
        simp only [«matches», Option.all_none, Bool.and_true]
        exact beq_false_of_ne (Ne.symm hg)
      rw [if_neg hg, if_neg (by simp [hm])]
      exact h.tag g
  · intro g y; simp only
    rw [hst, List.filter_cons]
    cases hp : e.ev.primaryId with
    | none =>
      have hm : «matches» g (some y) e = false := by simp [«matches», hp]
      simp only [hm, Bool.false_eq_true, if_false]
      exact h.key g y
    | some x =>
      simp only
      rw [PosMap.get_set _ _ _ _ h.keyPos]
      by_cases hgy : pairKey g y = pairKey e.ev.tag x
      · obtain ⟨hg, hy⟩ := pairKey_inj _ _ _ _ hgy
        subst hg; subst hy
        have hm : «matches» e.ev.tag (some y) e = true := by simp [«matches», hp]
        rw [if_pos rfl, if_pos hm, List.filter_cons, if_pos (by simp [hka]), List.map_cons, h.key]
      · have hm : «matches» g (some y) e = false := by
          simp only [«matches», hp, Option.all_some, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
            Option.some.injEq]
          by_cases hg : e.ev.tag = g
          · right; intro hxy; exact hgy (by rw [hg, hxy])
          · left; exact hg
        rw [if_neg hgy, if_neg (by simp [hm])]
        exact h.key g y
  · intro g j hj; simp only at hj
    rw [PosMap.get_set _ _ _ _ h.tagPos] at hj
    split at hj
    · rcases List.mem_cons.1 hj with rfl | hj
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.tagLt _ j hj) hb)
    · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.tagLt g j hj) hb)
  · intro q j hj; simp only at hj
    cases hp : e.ev.primaryId with
    | none => simp only [hp] at hj; exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.keyLt q j hj) hb)
    | some x =>
      simp only [hp] at hj
      rw [PosMap.get_set _ _ _ _ h.keyPos] at hj
      split at hj
      · rcases List.mem_cons.1 hj with rfl | hj
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.keyLt _ j hj) hb)
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.keyLt q j hj) hb)
  · intro j hj; exact h.above j (by omega)
  · simp only; rw [PosMap.size_set]; exact h.tagPos
  · simp only
    cases e.ev.primaryId with
    | none => exact h.keyPos
    | some x => simp only; rw [PosMap.size_set]; exact h.keyPos

theorem Inv.step {P : List (Entry × Nat)} {b : Nat} {s : MaskState} (h : Inv P b s)
    (e : Entry) (k : Nat) (hb : b ≤ k) (hk : k < s.dead.size) :
    Inv (P ++ [(e, k)]) (k + 1) (maskFastStep s (e, k)) ∧
      (maskFastStep s (e, k)).dead.size = s.dead.size := by
  cases hev : e.ev with
  | undo of_ id =>
    cases id with
    | none => exact h.step_undo_none e k of_ hev hb hk
    | some x => exact h.step_undo_some e k of_ x hev hb hk
  | _ => exact h.step_event e k (by simp [hev, Event.isUndo]) hb

theorem Inv.init (n : Nat) : Inv [] 0 (MaskState.init n) where
  stack := rfl
  tag := by intro g; simp [MaskState.init, PosMap.get_empty]
  key := by intro g x; simp [MaskState.init, PosMap.get_empty]
  tagLt := by intro g j hj; simp [MaskState.init, PosMap.get_empty] at hj
  keyLt := by intro g j hj; simp [MaskState.init, PosMap.get_empty] at hj
  above := by intro j _; simp only [MaskState.init, deadAt, Array.getElem?_replicate]; split <;> rfl
  posLt := by simp
  incr := List.Pairwise.nil
  tagPos := by simp [MaskState.init, PosMap.empty]
  keyPos := by simp [MaskState.init, PosMap.empty]

/-- **The simulation** (`maskFast_inv`): after the fast pass over `es` from position `n`, the invariant
holds of everything processed. -/
theorem maskFast_inv : ∀ (es : List Entry) (n : Nat) (P : List (Entry × Nat)) (s : MaskState),
    Inv P n s → n + es.length ≤ s.dead.size →
    Inv (P ++ es.zipIdx n) (n + es.length) ((es.zipIdx n).foldl maskFastStep s)
  | [], n, P, s, h, _ => by simpa using h
  | e :: es, n, P, s, h, hsz => by
    rw [List.zipIdx_cons, List.foldl_cons]
    have hk : n < s.dead.size := by simp at hsz; omega
    obtain ⟨h1, hsize⟩ := h.step e n (Nat.le_refl n) hk
    have := maskFast_inv es (n + 1) _ _ h1 (by rw [hsize]; simp at hsz; omega)
    simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using this

/-- The fast pass's dead set is the complement of the stack's positions. -/
theorem maskFast_stack (es : List Entry) :
    (stackI es).reverse = es.zipIdx.filter (fun p => !deadAt (maskFast es) p.2) := by
  have h := maskFast_inv es 0 [] (MaskState.init es.length) (Inv.init _) (by simp [MaskState.init])
  simpa [stackI, maskFast] using h.stack

theorem cancelledAt_eq_deadAt (es : List Entry) (p : Entry × Nat) (hp : p ∈ es.zipIdx) :
    cancelledAt es p.2 = deadAt (maskFast es) p.2 := by
  unfold cancelledAt
  have hiff : (stackI es).any (fun q => q.2 == p.2) = !deadAt (maskFast es) p.2 := by
    apply Bool.eq_iff_iff.2
    rw [List.any_eq_true]
    constructor
    · rintro ⟨q, hq, hqe⟩
      have : q ∈ (stackI es).reverse := List.mem_reverse.2 hq
      rw [maskFast_stack] at this
      have := (List.mem_filter.1 this).2
      simp only [beq_iff_eq] at hqe
      rwa [← hqe]
    · intro halive
      refine ⟨p, ?_, by simp⟩
      have : p ∈ (stackI es).reverse := by rw [maskFast_stack]; exact List.mem_filter.2 ⟨hp, halive⟩
      exact List.mem_reverse.1 this
  rw [hiff]; simp

/-- **The survivors are the entries at the positions not cancelled**, in file order: what ties the
cancelled line set on the wire to `survivors`. -/
theorem survivors_are_the_uncancelled_entries (es : List Entry) :
    survivors es = (es.zipIdx.filter (fun p => !cancelledAt es p.2)).map Prod.fst := by
  unfold survivors
  rw [← stackI_map, ← List.map_reverse, maskFast_stack]
  congr 1
  apply List.filter_congr
  intro p hp
  rw [cancelledAt_eq_deadAt es p hp]

@[csimp] theorem survivors_eq_survivorsFast : @survivors = @survivorsFast := by
  funext es
  unfold survivorsFast
  rw [survivors_are_the_uncancelled_entries]
  congr 1
  apply List.filter_congr
  intro p hp
  rw [cancelledAt_eq_deadAt es p hp]

@[csimp] theorem cancelledLines_eq_cancelledLinesFast : @cancelledLines = @cancelledLinesFast := by
  funext es
  unfold cancelledLines cancelledLinesFast
  congr 1
  apply List.filter_congr
  intro p hp
  rw [cancelledAt_eq_deadAt es p hp]

/-- A line is in the cancelled set exactly when its entry does not survive: the cancelled lines and the
survivors partition the entries. -/
theorem cancelled_and_survivors_partition (es : List Entry) :
    (es.zipIdx.filter (fun p => cancelledAt es p.2)).length + (survivors es).length = es.length := by
  rw [survivors_are_the_uncancelled_entries, List.length_map]
  have := List.length_eq_countP_add_countP (fun p : Entry × Nat => cancelledAt es p.2) (l := es.zipIdx)
  rw [List.length_zipIdx, List.countP_eq_length_filter, List.countP_eq_length_filter] at this
  rw [this]
  congr 2
  apply List.filter_congr
  intro p _; simp

/-! ## Witnesses (C1)

Each was probed in a scratch copy under `MemoryMax=8G timeout 120` (§14.0 item 4): at most 8 entries,
instants as `Nat` literals shared by every entry (the mask reads no time), no text parsed. -/

section Witnesses

/-- An entry at `line` whose instant and offset do not matter to the mask: 2026-09-07T06:05:00-05:00
(`Log.at0605`, `Log.cdt`). -/
def wEnt (line : Nat) (ev : Event) : Entry := ⟨line, Log.at0605, Log.cdt, ev⟩

def wDone (id : List Char) : Event :=
  .done id ⟨60, by decide⟩ ⟨60, by decide⟩ none [] ⟨3, by decide⟩ false

/-- **The mask ignores `isStateChange`** (inventory §2.2): a note is not a state change, and
`undo{of:"note"}` still cancels it. -/
theorem the_mask_ignores_isStateChange :
    Event.isStateChange (.note ['n']) = false ∧
    survivors [wEnt 1 (.note ['n']), wEnt 2 (.undo Log.Kind.note.tag none)] = [] := by
  decide

/-- The fork test `undo_mask_pairs_and_dangling`'s seven entries, lines 1–7: `done a`, `done b`,
`undo done a`, `undo done`, `undo done`, `note n`, `undo undo`. -/
def portedMask : List Entry :=
  [wEnt 1 (wDone ['a']), wEnt 2 (wDone ['b']), wEnt 3 (.undo Log.Kind.done.tag (some ['a'])),
   wEnt 4 (.undo Log.Kind.done.tag none), wEnt 5 (.undo Log.Kind.done.tag none), wEnt 6 (.note ['n']),
   wEnt 7 (.undo Log.Kind.undo.tag none)]

/-- **`undo_mask_pairs_and_dangling`, ported** (§7.1): `cancelled = [T,T,T,T,T,F,T]`, `dangling = [4, 6]`
(lines 5 and 7), `pairs() == 2`, and the one survivor is the note.  The cancelled line set the `log`
op answers is lines 1–5 and 7. -/
theorem undo_mask_pairs_and_dangling_ported :
    (List.range 7).map (cancelledAt portedMask) = [true, true, true, true, true, false, true] ∧
    (portedMask.filter (dangles portedMask)).map (·.line) = [5, 7] ∧
    ((List.range 7).countP (cancelledAt portedMask) - (portedMask.filter (dangles portedMask)).length) / 2 = 2 ∧
    (survivors portedMask).map (·.line) = [6] ∧
    cancelledLines portedMask = [1, 2, 3, 4, 5, 7] := by
  decide

/-- **Why `an_undo_of_an_undo_cancels_nothing_in_a_canonical_log` needs its hypothesis**: an `unknown`
event whose tag is `undo` (which no reader returns: `undo` is a known tag) is matched by
`undo{of:"undo"}`, exactly as the fork's `ev.name() == of` would match it. -/
theorem an_undo_of_an_undo_cancels_a_noncanonical_unknown_undo :
    ∃ (es : List Entry) (u : Entry), u.ev = .undo Log.Kind.undo.tag none ∧
      survivors (es ++ [u]) ≠ survivors es :=
  ⟨[wEnt 1 (.unknown Log.Kind.undo.tag [])], wEnt 2 (.undo Log.Kind.undo.tag none), rfl, by decide⟩

/-- **An undo with an id passes over a later event of another id** and cancels the latest of its
own; an undo without one takes the latest of the tag. -/
theorem an_undo_with_an_id_passes_over_other_ids :
    (survivors [wEnt 1 (wDone ['a']), wEnt 2 (wDone ['b']), wEnt 3 (.undo Log.Kind.done.tag (some ['a']))]).map (·.line) = [2] ∧
    (survivors [wEnt 1 (wDone ['a']), wEnt 2 (wDone ['b']), wEnt 3 (.undo Log.Kind.done.tag none)]).map (·.line) = [1] := by
  decide

end Witnesses

end Replay
end Tm
