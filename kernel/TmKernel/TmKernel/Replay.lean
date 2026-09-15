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

## C2: the day index (§6.2)

Fork `DayIndex` (inventory §2.3), built over the **surviving** wakes (`dayIndexOf`):

* `keptWakes`: the wake instants sorted in **chrono's order** (`DateTime`'s `Ord`, the UTC `(sec, ns)`
  pair, which is `Cal.Instant`'s `≤` and not `Instant.nanos`'s order at a leap second), then fork
  `dedup_by` on the local date in `cfg.tz`.  **The porting trap: `dedup_by` is consecutive.**  The index
  keeps the first wake of each *run* of one date, not the earliest wake per date; the two differ when
  local dates are not monotone in instant order, a clock falling back across midnight
  (`the_day_index_dedups_runs_not_dates`; T5's St John's arm).
* `lastWakeLe` is `last_wake_before` (`partition_point(|w| *w <= t)`), and `dayOf` is `day_of`: the
  wake's local date when `t.signed_duration_since(w) < Duration::hours(24)` by chrono's duration
  (`Cal.durationBetween`, its leap-second rule), otherwise `t`'s own local date.
* **Restated in chrono's order.**  §15's three C2 goals test `Instant.nanos`; each is false of the
  fork's index at a leap second (`dayOf_is_the_wake_date_within_a_day_by_nanos_is_refuted`,
  `a_wake_day_is_shorter_than_a_day_by_nanos_is_refuted`, `keptWakes_append_of_later_by_nanos_is_refuted`),
  and each is proved under its name with chrono's order and duration.
* **Quirk Q6(a), two "first wake" rules, ported faithfully** (gap 82).  The index keeps the earliest wake
  by instant per run; fork `DayReplay.wake` and `slept_by_day` (C5) read the first wake **in file order**
  attributed to the day (`firstLoggedWakeOn`).  `the_kept_wake_is_not_the_first_logged_wake` separates
  them on wakes appended out of time order, and
  `the_kept_wake_is_the_first_logged_wake_when_wakes_are_logged_in_order` shows that is the only way
  they differ.
* **Every entry has a day**, cancelled entries and undos included (`entryDays`, fork `ViewRow::day`):
  what the `log` op's `facts.days` carries.
* Not ported: `DayIndex::bounds`, `wake_of` (`keptWakeOn` exists only to state Q6(a)) and
  `local_midnight`, which have no caller outside `log.rs`.

**The fast twins.**  `sortWakes` is an insertion sort, which `decide` evaluates; it is compiled as
core's merge sort (`sortWakes_eq_sortWakesFast`, by `eq_of_perm_of_sorted`: a list sorted in an
antisymmetric order is determined by its elements).  `entryDays` looks each entry's wake up with a fold
over the kept wakes; it is compiled as a bisection over an array of them, which is the fork's
`partition_point` (`entryDays_eq_entryDaysFast`, by `lePoint_spec` and `lastWakeLe_of_point`, using
`keptWakes_sorted`).  Without it, a log of thirty thousand wakes costs a quadratic number of instant
comparisons.

## Rule D9-21 (functions here over a list the wire can make large)

`survivors`, `stackI`, `danglingOf` (`foldl`, specification only: compiled as their `@[csimp]` twins or
not called by the wire), `maskFast` (`foldl` of `maskFastStep`), `survivorsFast` and
`cancelledLinesFast` (`zipIdx`, `filterTR`, `mapTR`), `keyHash` (`foldl`), `pairKey`
(`flatMapTR`, `appendTR`), `PosMap.get` (`find?`), `PosMap.set` (`filterTR`), `List.dropWhile`
(a loop), and `Log.linesIncreasing` (the tail of `&&`; specification only).
C2 adds: `sortWakesFast` (core `mergeSort`, compiled as `mergeSortTR₂` behind core's `@[csimp]`;
it recurses on halves), the dedup (`foldl` of `keptStep`, then `reverse`), `wakeInstants` (`filterTR`,
`mapTR`), `entryDaysFast` (`mapTR` and one `toArray`), `lePoint` (a bisection, recursion depth
`log₂` of the wakes), and `Cal.localDate` (`offsetAt`, a `foldl` over at most 4,096 transitions).
Specification only, never on the wire: `insertWake` and `sortWakes` (compiled as their twin),
`lastWakeLe` and `entryDays` (compiled as `entryDaysFast`), and `keptWakeOn` and `firstLoggedWakeOn`
(`find?`, a loop; not called by the op).
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

/-! ## C2: the day index (§6.2) -/

section DayIndex

theorem instant_le_trans {a b c : Cal.Instant} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  rw [Cal.Instant.le_iff] at *; omega

theorem instant_le_refl (a : Cal.Instant) : a ≤ a := by
  rw [Cal.Instant.le_iff]; omega

theorem instant_le_of_not_le {a b : Cal.Instant} (h : ¬ a ≤ b) : b ≤ a := by
  rcases Cal.Instant.le_total a b with h' | h'
  · exact absurd h' h
  · exact h'

theorem instant_le_of_lt {a b : Cal.Instant} (h : a < b) : a ≤ b := by
  rw [Cal.Instant.le_iff]; rw [Cal.Instant.lt_iff] at h; omega

theorem instant_not_le_of_lt {a b : Cal.Instant} (h : a < b) : ¬ b ≤ a := by
  rw [Cal.Instant.le_iff]; rw [Cal.Instant.lt_iff] at h; omega

/-! ### `wakes.sort()` -/

/-- Insert into a list ascending in chrono's order, before the first element it is at or before. -/
def insertWake (w : Cal.Instant) : List Cal.Instant → List Cal.Instant
  | [] => [w]
  | x :: xs => if w ≤ x then w :: x :: xs else x :: insertWake w xs

/-- **`wakes.sort()`** in chrono's order (`DateTime`'s `Ord`, the UTC `(sec, ns)` pair): the
specification is an insertion sort, which `decide` evaluates; the code is core's merge sort
(`sortWakes_eq_sortWakesFast`). -/
def sortWakes (ws : List Cal.Instant) : List Cal.Instant := ws.foldr insertWake []

def sortWakesFast (ws : List Cal.Instant) : List Cal.Instant := ws.mergeSort (fun a b => decide (a ≤ b))

theorem insertWake_perm (w : Cal.Instant) : ∀ (l : List Cal.Instant), (insertWake w l).Perm (w :: l)
  | [] => List.Perm.refl _
  | x :: xs => by
    unfold insertWake
    split
    · exact List.Perm.refl _
    · exact ((insertWake_perm w xs).cons x).trans (List.Perm.swap w x xs)

theorem sortWakes_perm : ∀ (ws : List Cal.Instant), (sortWakes ws).Perm ws
  | [] => List.Perm.refl _
  | w :: ws => (insertWake_perm w _).trans ((sortWakes_perm ws).cons w)

theorem insertWake_sorted (w : Cal.Instant) : ∀ (l : List Cal.Instant), l.Pairwise (· ≤ ·) →
    (insertWake w l).Pairwise (· ≤ ·)
  | [], _ => List.pairwise_singleton _ _
  | x :: xs, h => by
    unfold insertWake
    split
    · rename_i hwx
      refine List.Pairwise.cons ?_ h
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hwx
      · exact instant_le_trans hwx (List.rel_of_pairwise_cons h hy)
    · rename_i hwx
      refine List.Pairwise.cons ?_ (insertWake_sorted w xs h.of_cons)
      intro y hy
      rcases List.mem_cons.1 ((insertWake_perm w xs).mem_iff.1 hy) with rfl | hy
      · exact instant_le_of_not_le hwx
      · exact List.rel_of_pairwise_cons h hy

theorem sortWakes_sorted : ∀ (ws : List Cal.Instant), (sortWakes ws).Pairwise (· ≤ ·)
  | [] => List.Pairwise.nil
  | w :: ws => insertWake_sorted w _ (sortWakes_sorted ws)

/-- **A list sorted in chrono's order is determined by its elements**: two sorted permutations of
one list are equal, because the order is antisymmetric on instants. -/
theorem eq_of_perm_of_sorted : ∀ {l₁ l₂ : List Cal.Instant}, l₁.Perm l₂ →
    l₁.Pairwise (· ≤ ·) → l₂.Pairwise (· ≤ ·) → l₁ = l₂
  | [], _, h, _, _ => h.nil_eq
  | _ :: _, [], h, _, _ => h.eq_nil
  | a :: t₁, b :: t₂, h, h₁, h₂ => by
    have hab : a ≤ b := by
      rcases List.mem_cons.1 (h.mem_iff.2 List.mem_cons_self) with hb | hb
      · rw [hb]; exact instant_le_refl _
      · exact List.rel_of_pairwise_cons h₁ hb
    have hba : b ≤ a := by
      rcases List.mem_cons.1 (h.mem_iff.1 List.mem_cons_self) with ha | ha
      · rw [ha]; exact instant_le_refl _
      · exact List.rel_of_pairwise_cons h₂ ha
    have := Cal.Instant.le_antisymm hab hba
    subst this
    rw [eq_of_perm_of_sorted (List.perm_cons a |>.1 h) h₁.of_cons h₂.of_cons]

@[csimp] theorem sortWakes_eq_sortWakesFast : @sortWakes = @sortWakesFast := by
  funext ws
  apply eq_of_perm_of_sorted ((sortWakes_perm ws).trans (List.mergeSort_perm ws _).symm)
    (sortWakes_sorted ws)
  have := List.pairwise_mergeSort (le := fun a b : Cal.Instant => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact instant_le_trans hab hbc)
    (fun a b => by rcases Cal.Instant.le_total a b with h | h <;> simp [h]) ws
  exact this.imp (fun h => by simpa using h)

/-- Two lists each sorted, every element of the first before every element of the second, sort as
their concatenation. -/
theorem sortWakes_append_of_later (ws₁ ws₂ : List Cal.Instant) (h : ∀ a ∈ ws₁, ∀ b ∈ ws₂, a < b) :
    sortWakes (ws₁ ++ ws₂) = sortWakes ws₁ ++ sortWakes ws₂ := by
  apply eq_of_perm_of_sorted
  · exact (sortWakes_perm _).trans ((sortWakes_perm ws₁).append (sortWakes_perm ws₂)).symm
  · exact sortWakes_sorted _
  · rw [List.pairwise_append]
    refine ⟨sortWakes_sorted _, sortWakes_sorted _, fun a ha b hb => ?_⟩
    exact instant_le_of_lt (h a ((sortWakes_perm ws₁).mem_iff.1 ha) b ((sortWakes_perm ws₂).mem_iff.1 hb))

/-! ### `dedup_by` on the date: the first of each run of one date -/

/-- One step of fork `dedup_by(|later, kept| later's date == kept's date)`: the state is the last
kept wake and the kept wakes, most recent first.  A wake whose local date in `z` is the last kept
wake's is dropped; any other is kept. -/
def keptStep (z : Cal.Tz) (acc : Option Cal.Instant × List Cal.Instant) (w : Cal.Instant) :
    Option Cal.Instant × List Cal.Instant :=
  match acc.1 with
  | some k => if Cal.localDate z w = Cal.localDate z k then acc else (some w, w :: acc.2)
  | none => (some w, w :: acc.2)

/-- The dedup over `ws` in the order given, continuing a run whose last kept wake is `last`. -/
def dedupFrom (z : Cal.Tz) (last : Option Cal.Instant) (ws : List Cal.Instant) : List Cal.Instant :=
  (ws.foldl (keptStep z) (last, [])).2.reverse

/-- **Continue a day index**: sort `ws`, then dedup it continuing the run whose last kept wake is
`last` (§6.2's `keptFrom`, what `keptWakes_append_of_later` needs). -/
def keptFrom (z : Cal.Tz) (last : Option Cal.Instant) (ws : List Cal.Instant) : List Cal.Instant :=
  dedupFrom z last (sortWakes ws)

/-- **Fork `DayIndex::new`**: the wakes sorted in chrono's order, then **consecutive** dedup on the
local date in `z`, keeping the first of each run.  Not "the earliest wake per date": the two differ
when local dates are not monotone in instant order (a fold at midnight). -/
def keptWakes (z : Cal.Tz) (ws : List Cal.Instant) : List Cal.Instant := keptFrom z none ws

theorem foldl_keptStep_acc (z : Cal.Tz) : ∀ (xs : List Cal.Instant) (l : Option Cal.Instant)
    (acc : List Cal.Instant),
    xs.foldl (keptStep z) (l, acc)
      = ((xs.foldl (keptStep z) (l, [])).1, (xs.foldl (keptStep z) (l, [])).2 ++ acc)
  | [], _, _ => rfl
  | x :: xs, l, acc => by
    rw [List.foldl_cons, List.foldl_cons]
    cases l with
    | none =>
      simp only [keptStep]
      rw [foldl_keptStep_acc z xs (some x) (x :: acc), foldl_keptStep_acc z xs (some x) [x]]
      simp
    | some k =>
      simp only [keptStep]
      split
      · rw [foldl_keptStep_acc z xs (some k) acc]
      · rw [foldl_keptStep_acc z xs (some x) (x :: acc), foldl_keptStep_acc z xs (some x) [x]]
        simp

theorem foldl_keptStep_head (z : Cal.Tz) (l : Option Cal.Instant) : ∀ (xs : List Cal.Instant)
    (s : Option Cal.Instant × List Cal.Instant), s.1 = s.2.head?.or l →
    (xs.foldl (keptStep z) s).1 = (xs.foldl (keptStep z) s).2.head?.or l
  | [], _, h => h
  | x :: xs, s, h => by
    rw [List.foldl_cons]
    apply foldl_keptStep_head z l xs
    obtain ⟨s1, s2⟩ := s
    unfold keptStep
    cases s1 with
    | none => simp
    | some k =>
      simp only
      split
      · exact h
      · simp

theorem keptWakes_last (z : Cal.Tz) (ws : List Cal.Instant) :
    ((sortWakes ws).foldl (keptStep z) (none, [])).1 = (keptWakes z ws).getLast? := by
  rw [foldl_keptStep_head z none _ _ rfl]
  simp [keptWakes, keptFrom, dedupFrom]

/-- `keptWakes_append_of_later` (Goals, §15, C2), **restated in chrono's order** (carried note 1: the
fork sorts `DateTime`s, whose order is not `Instant.nanos`'s at a leap second): when every wake of
`ws₁` is before every wake of `ws₂`, the day index of both is `ws₁`'s continued by `ws₂`'s. -/
theorem keptWakes_append_of_later (z : Cal.Tz) (ws₁ ws₂ : List Cal.Instant)
    (h : ∀ a ∈ ws₁, ∀ b ∈ ws₂, a < b) :
    keptWakes z (ws₁ ++ ws₂) = keptWakes z ws₁ ++ keptFrom z (keptWakes z ws₁).getLast? ws₂ := by
  unfold keptWakes keptFrom dedupFrom
  rw [sortWakes_append_of_later ws₁ ws₂ h, List.foldl_append]
  rw [foldl_keptStep_acc z (sortWakes ws₂)]
  simp only [List.reverse_append]
  have := keptWakes_last z ws₁
  unfold keptWakes keptFrom dedupFrom at this
  rw [this]

theorem mem_foldl_keptStep (z : Cal.Tz) : ∀ (xs : List Cal.Instant) (s : Option Cal.Instant × List Cal.Instant)
    (x : Cal.Instant), x ∈ (xs.foldl (keptStep z) s).2 → x ∈ s.2 ∨ x ∈ xs
  | [], _, _, h => Or.inl h
  | y :: xs, s, x, h => by
    rw [List.foldl_cons] at h
    rcases mem_foldl_keptStep z xs _ x h with h | h
    · obtain ⟨s1, s2⟩ := s
      unfold keptStep at h
      cases s1 with
      | none =>
        rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr List.mem_cons_self
        · exact Or.inl h
      | some k =>
        simp only at h
        split at h
        · exact Or.inl h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inr List.mem_cons_self
          · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- Every wake the index keeps was one of the wakes. -/
theorem mem_of_mem_keptFrom (z : Cal.Tz) (last : Option Cal.Instant) (ws : List Cal.Instant)
    (x : Cal.Instant) (h : x ∈ keptFrom z last ws) : x ∈ ws := by
  unfold keptFrom dedupFrom at h
  rw [List.mem_reverse] at h
  rcases mem_foldl_keptStep z _ _ x h with h | h
  · simp at h
  · exact (sortWakes_perm ws).mem_iff.1 h

theorem foldl_keptStep_sublist (z : Cal.Tz) : ∀ (xs : List Cal.Instant) (l : Option Cal.Instant),
    (xs.foldl (keptStep z) (l, [])).2.reverse.Sublist xs
  | [], _ => List.Sublist.slnil
  | x :: xs, l => by
    rw [List.foldl_cons]
    cases l with
    | none =>
      simp only [keptStep]
      rw [foldl_keptStep_acc z xs (some x) [x]]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append]
      exact (foldl_keptStep_sublist z xs (some x)).cons_cons x
    | some k =>
      simp only [keptStep]
      split
      · exact (foldl_keptStep_sublist z xs (some k)).cons x
      · rw [foldl_keptStep_acc z xs (some x) [x]]
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append]
        exact (foldl_keptStep_sublist z xs (some x)).cons_cons x

/-- **The kept wakes are in chrono's order.** -/
theorem keptWakes_sorted (z : Cal.Tz) (ws : List Cal.Instant) : (keptWakes z ws).Pairwise (· ≤ ·) :=
  (sortWakes_sorted ws).sublist (foldl_keptStep_sublist z _ none)

/-! ### `last_wake_before` and `day_of` -/

/-- **Fork `DayIndex::last_wake_before`**: the last wake at or before `t` in chrono's order.  The fork
reads it with `partition_point` over its sorted vector; over a sorted list that is the last element
`≤ t` in list order, which is this fold (`lastWakeLeArr_eq_lastWakeLe`, the compiled bisection). -/
def lastWakeLe (kw : List Cal.Instant) (t : Cal.Instant) : Option Cal.Instant :=
  kw.foldl (fun acc w => if w ≤ t then some w else acc) none

/-- **Fork `DayIndex::day_of`**: the local date in `z` of the last wake at or before `t` when
`t.signed_duration_since(w) < Duration::hours(24)`, otherwise `t`'s own local date.  chrono's
duration is `Cal.durationBetween` (its leap-second rule), and a `TimeDelta` below 24 hours has fewer
than 86,400 whole seconds, whatever its nanoseconds. -/
def dayOf (z : Cal.Tz) (kw : List Cal.Instant) (t : Cal.Instant) : Nat :=
  match lastWakeLe kw t with
  | some w => if (Cal.durationBetween w t).1 < 86400 then Cal.localDate z w else Cal.localDate z t
  | none => Cal.localDate z t

theorem foldl_lastWake_or (t : Cal.Instant) : ∀ (kw : List Cal.Instant) (acc : Option Cal.Instant),
    kw.foldl (fun acc w => if w ≤ t then some w else acc) acc = (lastWakeLe kw t).or acc
  | [], acc => by simp [lastWakeLe]
  | w :: kw, acc => by
    unfold lastWakeLe
    rw [List.foldl_cons, List.foldl_cons, foldl_lastWake_or t kw, foldl_lastWake_or t kw]
    by_cases h : w ≤ t <;> simp [h]

/-- The wake found is at or before `t`, and one of the wakes. -/
theorem lastWakeLe_cons (w : Cal.Instant) (kw : List Cal.Instant) (t : Cal.Instant) :
    lastWakeLe (w :: kw) t = (lastWakeLe kw t).or (if w ≤ t then some w else none) := by
  unfold lastWakeLe
  rw [List.foldl_cons, foldl_lastWake_or]
  rfl

theorem lastWakeLe_le : ∀ (kw : List Cal.Instant) (t w : Cal.Instant), lastWakeLe kw t = some w →
    w ≤ t ∧ w ∈ kw
  | [], _, _, h => by simp [lastWakeLe] at h
  | x :: kw, t, w, h => by
    rw [lastWakeLe_cons] at h
    cases hl : lastWakeLe kw t with
    | some y =>
      rw [hl] at h
      simp only [Option.some_or, Option.some.injEq] at h
      subst h
      exact ⟨(lastWakeLe_le kw t y hl).1, List.mem_cons_of_mem _ (lastWakeLe_le kw t y hl).2⟩
    | none =>
      rw [hl] at h
      by_cases hx : x ≤ t
      · simp only [hx, if_true, Option.none_or, Option.some.injEq] at h
        subst h
        exact ⟨hx, List.mem_cons_self⟩
      · simp [hx] at h

/-- A later list of wakes, every one after `t`, does not move `t`'s last wake. -/
theorem lastWakeLe_append_of_later (l₁ l₂ : List Cal.Instant) (t : Cal.Instant)
    (h : ∀ b ∈ l₂, t < b) : lastWakeLe (l₁ ++ l₂) t = lastWakeLe l₁ t := by
  unfold lastWakeLe
  rw [List.foldl_append, foldl_lastWake_or]
  have : lastWakeLe l₂ t = none := by
    cases hl : lastWakeLe l₂ t with
    | none => rfl
    | some w =>
      obtain ⟨hle, hmem⟩ := lastWakeLe_le l₂ t w hl
      exact absurd hle (instant_not_le_of_lt (h w hmem))
  rw [this]
  rfl

/-- `dayOf_is_the_wake_date_within_a_day` (Goals, §15, C2), **restated in chrono's order**: the
hypothesis is chrono's `signed_duration_since(w) < 24 h`, not `t.nanos < w.nanos + 86400·10^9`
(`dayOf_is_the_wake_date_within_a_day_by_nanos_is_refuted`). -/
theorem dayOf_is_the_wake_date_within_a_day (z : Cal.Tz) (kw : List Cal.Instant) (t w : Cal.Instant)
    (hw : lastWakeLe kw t = some w) (h24 : (Cal.durationBetween w t).1 < 86400) :
    dayOf z kw t = Cal.localDate z w := by
  simp [dayOf, hw, h24]

theorem dayOf_without_a_recent_wake_is_the_local_date (z : Cal.Tz) (kw : List Cal.Instant)
    (t : Cal.Instant) (h : ∀ w, lastWakeLe kw t = some w → 86400 ≤ (Cal.durationBetween w t).1) :
    dayOf z kw t = Cal.localDate z t := by
  unfold dayOf
  cases hw : lastWakeLe kw t with
  | none => rfl
  | some w => simp [Int.not_lt.2 (h w hw)]

/-- `a_wake_day_is_shorter_than_a_day` (Goals, §15, C2), **restated in chrono's order**: an instant
attributed to its wake's date, which is not its own, is under 24 hours of chrono's duration after
that wake. -/
theorem a_wake_day_is_shorter_than_a_day (z : Cal.Tz) (ws : List Cal.Instant) (t w : Cal.Instant)
    (hw : lastWakeLe (keptWakes z ws) t = some w)
    (hd : dayOf z (keptWakes z ws) t = Cal.localDate z w)
    (hne : Cal.localDate z t ≠ Cal.localDate z w) :
    (Cal.durationBetween w t).1 < 86400 := by
  unfold dayOf at hd
  rw [hw] at hd
  simp only at hd
  split at hd
  · assumption
  · exact absurd hd hne

/-- **The locality W2 needs** (§6.2, §9.5): wakes appended later, all after `t`, do not change `t`'s
day. -/
theorem dayOf_agrees_below_a_later_wake (z : Cal.Tz) (ws₁ ws₂ : List Cal.Instant) (t : Cal.Instant)
    (h : ∀ a ∈ ws₁, ∀ b ∈ ws₂, a < b) (ht : ∀ b ∈ ws₂, t < b) :
    dayOf z (keptWakes z (ws₁ ++ ws₂)) t = dayOf z (keptWakes z ws₁) t := by
  rw [keptWakes_append_of_later z ws₁ ws₂ h]
  unfold dayOf
  rw [lastWakeLe_append_of_later _ _ t (fun b hb => ht b (mem_of_mem_keptFrom z _ ws₂ b hb))]

/-- **An instant off its own date belongs to a wake under a day before it**: whenever `dayOf` is not
`t`'s local date, there is a kept wake at or before `t`, of that date, under 24 hours of chrono's
duration earlier.  What "a day is never longer than 24 hours" says, for every index. -/
theorem an_instant_off_its_own_date_is_within_a_day_of_its_wake (z : Cal.Tz) (kw : List Cal.Instant)
    (t : Cal.Instant) (h : dayOf z kw t ≠ Cal.localDate z t) :
    ∃ w, lastWakeLe kw t = some w ∧ w ∈ kw ∧ w ≤ t ∧ dayOf z kw t = Cal.localDate z w ∧
      (Cal.durationBetween w t).1 < 86400 := by
  unfold dayOf at *
  cases hw : lastWakeLe kw t with
  | none => rw [hw] at h; exact absurd rfl h
  | some w =>
    rw [hw] at h
    simp only at h ⊢
    obtain ⟨hle, hmem⟩ := lastWakeLe_le kw t w hw
    by_cases h24 : (Cal.durationBetween w t).1 < 86400
    · exact ⟨w, rfl, hmem, hle, by simp [h24], h24⟩
    · simp [h24] at h

/-! ### The index of a log, and quirk Q6(a): two "first wake" rules -/

def isWake (e : Entry) : Bool :=
  match e.ev with
  | .wake _ _ => true
  | _ => false

/-- The survivors' wake instants, in file order (fork `refs.filter(Wake).map(t)`). -/
def wakeInstants (sv : List Entry) : List Cal.Instant := (sv.filter isWake).map (fun e => e.t.val)

/-- **The day index of a log**: the kept wakes of its surviving wakes (fork `replay_lines`'
`DayIndex::new(tz, refs…)`). -/
def dayIndexOf (z : Cal.Tz) (es : List Entry) : List Cal.Instant := keptWakes z (wakeInstants (survivors es))

/-- Fork `DayIndex::wake_of`: the first kept wake whose local date is `d`.  Not on the wire (§6.2: no
caller outside `log.rs`); it states quirk Q6(a). -/
def keptWakeOn (z : Cal.Tz) (kw : List Cal.Instant) (d : Nat) : Option Cal.Instant :=
  kw.find? (fun w => Cal.localDate z w == d)

/-- **The first logged wake of day `d`**: the first entry **in file order** that is a wake attributed to
`d` (fork `DayReplay.wake`'s `if d.wake.is_none()` and `slept_by_day`'s `or_insert`; C5 reads it). -/
def firstLoggedWakeOn (z : Cal.Tz) (kw : List Cal.Instant) (es : List Entry) (d : Nat) : Option Entry :=
  es.find? (fun e => isWake e && dayOf z kw e.t.val == d)

theorem dedupFrom_append (z : Cal.Tz) (l : Option Cal.Instant) (V U : List Cal.Instant) :
    dedupFrom z l (V ++ U) = dedupFrom z l V ++ dedupFrom z (V.foldl (keptStep z) (l, [])).1 U := by
  unfold dedupFrom
  rw [List.foldl_append]
  have : V.foldl (keptStep z) (l, []) = ((V.foldl (keptStep z) (l, [])).1, (V.foldl (keptStep z) (l, [])).2) := rfl
  rw [this, foldl_keptStep_acc z U]
  simp

theorem dedupFrom_last (z : Cal.Tz) (V : List Cal.Instant) :
    (V.foldl (keptStep z) (none, [])).1 = (dedupFrom z none V).getLast? := by
  rw [foldl_keptStep_head z none V _ rfl]
  simp [dedupFrom]

theorem dedupFrom_single (z : Cal.Tz) (L : Option Cal.Instant) (x : Cal.Instant) :
    dedupFrom z L [x]
      = (match L with | some k => if Cal.localDate z x = Cal.localDate z k then [] else [x] | none => [x]) := by
  cases L with
  | none => rfl
  | some k =>
    simp only [dedupFrom, List.foldl_cons, List.foldl_nil, keptStep]
    split <;> rfl

theorem lastWakeLe_snoc (l : List Cal.Instant) (x t : Cal.Instant) :
    lastWakeLe (l ++ [x]) t = if x ≤ t then some x else lastWakeLe l t := by
  unfold lastWakeLe
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem lastWakeLe_of_all_le (t : Cal.Instant) : ∀ (l : List Cal.Instant), (∀ y ∈ l, y ≤ t) →
    lastWakeLe l t = l.getLast?
  | [], _ => rfl
  | x :: xs, h => by
    rw [lastWakeLe_cons, lastWakeLe_of_all_le t xs (fun y hy => h y (List.mem_cons_of_mem _ hy)),
      if_pos (h x List.mem_cons_self), List.getLast?_cons]
    cases xs.getLast? <;> rfl

/-- **In a sorted list of wakes, each wake's last kept wake is of its own date**: the run a wake
belongs to began at a kept wake of its date, and a later kept wake at or before it equals it. -/
theorem lastWakeLe_dedup_same_date (z : Cal.Tz) : ∀ (R : List Cal.Instant), R.reverse.Pairwise (· ≤ ·) →
    ∀ w ∈ R.reverse, ∃ k, lastWakeLe (dedupFrom z none R.reverse) w = some k ∧
      Cal.localDate z k = Cal.localDate z w
  | [], _, w, hw => by simp at hw
  | x :: R, hs, w, hw => by
    simp only [List.reverse_cons] at hs hw ⊢
    obtain ⟨hsV, -, hVx⟩ := List.pairwise_append.1 hs
    have hle : ∀ v ∈ R.reverse, v ≤ x := fun v hv => hVx v hv x List.mem_cons_self
    have hK : ∀ y ∈ dedupFrom z none R.reverse, y ≤ x := fun y hy =>
      hle y ((foldl_keptStep_sublist z R.reverse none).subset hy)
    rw [dedupFrom_append, dedupFrom_last, dedupFrom_single]
    rcases List.mem_append.1 hw with hw | hw
    · obtain ⟨k, hk, hkd⟩ := lastWakeLe_dedup_same_date z R hsV w hw
      have hkeep : ∀ (tail : List Cal.Instant), (tail = [] ∨ tail = [x]) →
          ∃ k, lastWakeLe (dedupFrom z none R.reverse ++ tail) w = some k ∧
            Cal.localDate z k = Cal.localDate z w := by
        intro tail ht
        rcases ht with rfl | rfl
        · exact ⟨k, by rw [List.append_nil]; exact hk, hkd⟩
        · rw [lastWakeLe_snoc]
          by_cases hxw : x ≤ w
          · rw [if_pos hxw]
            exact ⟨x, rfl, by rw [Cal.Instant.le_antisymm hxw (hle w hw)]⟩
          · rw [if_neg hxw]; exact ⟨k, hk, hkd⟩
      apply hkeep
      split
      · split
        · exact Or.inl rfl
        · exact Or.inr rfl
      · exact Or.inr rfl
    · simp only [List.mem_singleton] at hw
      subst hw
      cases hL : (dedupFrom z none R.reverse).getLast? with
      | none => exact ⟨w, by rw [lastWakeLe_snoc, if_pos (instant_le_refl w)], rfl⟩
      | some k =>
        simp only
        split
        · rename_i hdate
          refine ⟨k, ?_, hdate.symm⟩
          rw [List.append_nil, lastWakeLe_of_all_le w _ hK, hL]
        · exact ⟨w, by rw [lastWakeLe_snoc, if_pos (instant_le_refl w)], rfl⟩

/-- **A logged wake belongs to its own date** when the wakes are in chrono's order. -/
theorem a_wake_is_on_its_own_date (z : Cal.Tz) (W : List Cal.Instant) (hs : W.Pairwise (· ≤ ·))
    (w : Cal.Instant) (hw : w ∈ W) : dayOf z (keptWakes z W) w = Cal.localDate z w := by
  have hsort : sortWakes W = W := eq_of_perm_of_sorted (sortWakes_perm W) (sortWakes_sorted W) hs
  have := lastWakeLe_dedup_same_date z W.reverse (by rw [List.reverse_reverse]; exact hs) w
    (by rw [List.reverse_reverse]; exact hw)
  rw [List.reverse_reverse] at this
  obtain ⟨k, hk, hkd⟩ := this
  unfold dayOf keptWakes keptFrom
  rw [hsort, hk]
  simp only
  split <;> simp [hkd]

theorem find?_congr_mem {α : Type} : ∀ (l : List α) (p q : α → Bool), (∀ a ∈ l, p a = q a) →
    l.find? p = l.find? q
  | [], _, _, _ => rfl
  | x :: xs, p, q, h => by
    rw [List.find?_cons, List.find?_cons, h x List.mem_cons_self,
      find?_congr_mem xs p q (fun a ha => h a (List.mem_cons_of_mem _ ha))]

theorem find?_dedupFrom (z : Cal.Tz) (d : Nat) : ∀ (W : List Cal.Instant) (last : Option Cal.Instant),
    (∀ k, last = some k → Cal.localDate z k ≠ d) →
    (dedupFrom z last W).find? (fun w => Cal.localDate z w == d) = W.find? (fun w => Cal.localDate z w == d)
  | [], _, _ => rfl
  | x :: xs, last, h => by
    have hcons : dedupFrom z last (x :: xs)
        = dedupFrom z last [x] ++ dedupFrom z ((keptStep z (last, []) x).1) xs := by
      rw [show x :: xs = [x] ++ xs from rfl, dedupFrom_append]; rfl
    rw [hcons, dedupFrom_single, List.find?_append]
    cases last with
    | none =>
      simp only [keptStep]
      by_cases hx : Cal.localDate z x = d
      · simp [hx]
      · have ih := find?_dedupFrom z d xs (some x) (fun k hk => by cases hk; exact hx)
        simp [hx, ih]
    | some k =>
      simp only [keptStep]
      by_cases hxk : Cal.localDate z x = Cal.localDate z k
      · have hx : Cal.localDate z x ≠ d := by rw [hxk]; exact h k rfl
        have ih := find?_dedupFrom z d xs (some k) h
        rw [if_pos hxk, if_pos hxk, List.find?_nil, Option.none_or, ih, List.find?_cons,
          beq_eq_false_iff_ne.2 hx]
      · rw [if_neg hxk, if_neg hxk, List.find?_cons, List.find?_nil, List.find?_cons]
        by_cases hx : Cal.localDate z x = d
        · rw [beq_iff_eq.2 hx]; rfl
        · have ih := find?_dedupFrom z d xs (some x) (fun k hk => by cases hk; exact hx)
          rw [beq_eq_false_iff_ne.2 hx]
          simpa using ih

/-- **Quirk Q6(a)'s other direction: in-order wakes make the two rules one.**  When the surviving
wakes are logged in chrono's order, the first kept wake of a date is the first logged wake of that
day; the rules differ only on wakes appended out of time order
(`the_kept_wake_is_not_the_first_logged_wake`). -/
theorem the_kept_wake_is_the_first_logged_wake_when_wakes_are_logged_in_order (z : Cal.Tz)
    (es : List Entry) (d : Nat) (hs : (wakeInstants (survivors es)).Pairwise (· ≤ ·)) :
    keptWakeOn z (dayIndexOf z es) d
      = (firstLoggedWakeOn z (dayIndexOf z es) (survivors es) d).map (fun e => e.t.val) := by
  have hsort : sortWakes (wakeInstants (survivors es)) = wakeInstants (survivors es) :=
    eq_of_perm_of_sorted (sortWakes_perm _) (sortWakes_sorted _) hs
  unfold keptWakeOn firstLoggedWakeOn
  have hl : (dayIndexOf z es).find? (fun w => Cal.localDate z w == d)
      = (wakeInstants (survivors es)).find? (fun w => Cal.localDate z w == d) := by
    unfold dayIndexOf keptWakes keptFrom
    rw [hsort]
    exact find?_dedupFrom z d _ none (fun k hk => by cases hk)
  rw [hl]
  have hr : (wakeInstants (survivors es)).find? (fun w => Cal.localDate z w == d)
      = (wakeInstants (survivors es)).find? (fun w => dayOf z (dayIndexOf z es) w == d) := by
    apply find?_congr_mem
    intro w hw
    rw [dayIndexOf, a_wake_is_on_its_own_date z _ hs w hw]
  rw [hr]
  unfold wakeInstants
  rw [List.find?_map, List.find?_filter]
  congr 1
  apply find?_congr_mem
  intro e _
  simp only [Function.comp_apply, Bool.decide_and, Bool.decide_eq_true]

/-! ### Every entry's day, on the wire, and its compiled twin -/

/-- **Every entry's day** (fork `ViewRow::day`): `(line, dayOf)` for every entry in file order,
cancelled entries and undos included, over the day index of the survivors' wakes. -/
def entryDays (z : Cal.Tz) (es : List Entry) : List (Nat × Nat) :=
  let kw := dayIndexOf z es
  es.map (fun e => (e.line, dayOf z kw e.t.val))

/-- **Fork `partition_point(|w| *w <= t)`**: the number of wakes at or before `t` in an ascending
array, by bisection of `[lo, hi)`. -/
def lePoint (a : Array Cal.Instant) (t : Cal.Instant) (lo hi : Nat) : Nat :=
  if _h : lo < hi then
    match a[(lo + hi) / 2]? with
    | some w => if w ≤ t then lePoint a t ((lo + hi) / 2 + 1) hi else lePoint a t lo ((lo + hi) / 2)
    | none => lo
  else lo
termination_by hi - lo
decreasing_by all_goals omega

def lastWakeLeArr (a : Array Cal.Instant) (t : Cal.Instant) : Option Cal.Instant :=
  match lePoint a t 0 a.size with
  | 0 => none
  | p + 1 => a[p]?

def dayOfArr (z : Cal.Tz) (a : Array Cal.Instant) (t : Cal.Instant) : Nat :=
  match lastWakeLeArr a t with
  | some w => if (Cal.durationBetween w t).1 < 86400 then Cal.localDate z w else Cal.localDate z t
  | none => Cal.localDate z t

def entryDaysFast (z : Cal.Tz) (es : List Entry) : List (Nat × Nat) :=
  let a := (dayIndexOf z es).toArray
  es.map (fun e => (e.line, dayOfArr z a e.t.val))

theorem lePoint_spec (l : List Cal.Instant) (hs : l.Pairwise (· ≤ ·)) (t : Cal.Instant) (lo hi : Nat)
    (hlh : lo ≤ hi) (hn : hi ≤ l.length)
    (hlo : ∀ i (hi' : i < l.length), i < lo → l[i] ≤ t)
    (hhi : ∀ i (hi' : i < l.length), hi ≤ i → ¬ l[i] ≤ t) :
    lePoint l.toArray t lo hi ≤ l.length ∧
    (∀ i (h : i < l.length), i < lePoint l.toArray t lo hi → l[i] ≤ t) ∧
    (∀ i (h : i < l.length), lePoint l.toArray t lo hi ≤ i → ¬ l[i] ≤ t) := by
  rw [lePoint]
  split
  · rename_i h
    have hm : (lo + hi) / 2 < l.length := by omega
    rw [List.getElem?_toArray, List.getElem?_eq_getElem hm]
    simp only
    split
    · rename_i hle
      apply lePoint_spec l hs t _ hi (by omega) hn
      · intro i hi' hi2
        by_cases hlt : i < lo
        · exact hlo i hi' hlt
        · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi2) with hi3 | hi3
          · exact instant_le_trans (List.pairwise_iff_getElem.1 hs i _ hi' hm hi3) hle
          · simp only [hi3]; exact hle
      · exact hhi
    · rename_i hle
      apply lePoint_spec l hs t lo _ (by omega) (by omega) hlo
      intro i hi' hi2
      rcases Nat.lt_or_eq_of_le hi2 with hi3 | hi3
      · intro hc; exact hle (instant_le_trans (List.pairwise_iff_getElem.1 hs _ i hm hi' hi3) hc)
      · simp only [← hi3]; exact hle
  · refine ⟨by omega, fun i hi' hi2 => hlo i hi' hi2, fun i hi' hi2 => hhi i hi' (by omega)⟩
termination_by hi - lo
decreasing_by all_goals omega

theorem lastWakeLe_of_point (t : Cal.Instant) : ∀ (l : List Cal.Instant) (p : Nat), p ≤ l.length →
    (∀ i (h : i < l.length), i < p → l[i] ≤ t) →
    (∀ i (h : i < l.length), p ≤ i → ¬ l[i] ≤ t) →
    lastWakeLe l t = (match p with | 0 => none | q + 1 => l[q]?)
  | [], p, hp, _, _ => by
    simp at hp; subst hp; rfl
  | x :: xs, 0, _, _, h2 => by
    have ih := lastWakeLe_of_point t xs 0 (Nat.zero_le _) (fun i _ hi => absurd hi (Nat.not_lt_zero _))
      (fun i h _ => by have := h2 (i + 1) (by simp; omega) (Nat.zero_le _); rwa [List.getElem_cons_succ] at this)
    simp only at ih ⊢
    rw [lastWakeLe_cons, ih, if_neg (by have := h2 0 (by simp) (Nat.le_refl 0); rwa [List.getElem_cons_zero] at this)]
    rfl
  | x :: xs, q + 1, hp, h1, h2 => by
    have hx : x ≤ t := by have := h1 0 (by simp) (Nat.succ_pos _); rwa [List.getElem_cons_zero] at this
    have ih := lastWakeLe_of_point t xs q (by simp at hp; omega)
      (fun i h hi => by have := h1 (i + 1) (by simp; omega) (by omega); rwa [List.getElem_cons_succ] at this)
      (fun i h hi => by have := h2 (i + 1) (by simp; omega) (by omega); rwa [List.getElem_cons_succ] at this)
    rw [lastWakeLe_cons, ih, if_pos hx]
    cases q with
    | zero => rfl
    | succ r =>
      have hr : r < xs.length := by simp at hp; omega
      simp [List.getElem?_eq_getElem hr]

/-- **The bisection is the fold** on an ascending list. -/
theorem lastWakeLeArr_eq_lastWakeLe (l : List Cal.Instant) (hs : l.Pairwise (· ≤ ·)) (t : Cal.Instant) :
    lastWakeLeArr l.toArray t = lastWakeLe l t := by
  obtain ⟨hp, h1, h2⟩ := lePoint_spec l hs t 0 l.length (Nat.zero_le _) (Nat.le_refl _)
    (fun i _ h => absurd h (Nat.not_lt_zero _)) (fun i hi h => absurd hi (Nat.not_lt.2 h))
  rw [lastWakeLe_of_point t l _ hp h1 h2]
  unfold lastWakeLeArr
  simp only [List.size_toArray]
  split <;> simp_all

@[csimp] theorem entryDays_eq_entryDaysFast : @entryDays = @entryDaysFast := by
  funext z es
  unfold entryDays entryDaysFast
  simp only
  apply List.map_congr_left
  intro e _
  unfold dayOfArr dayOf dayIndexOf
  rw [lastWakeLeArr_eq_lastWakeLe _ (keptWakes_sorted z _)]

end DayIndex



/-! ## Witnesses (C2)

Each was probed in a scratch copy under `MemoryMax=8G timeout 120` (§14.0 item 4): at most 3 entries
or 3 wakes, at most 2 zone transitions (`Cal.chicago`'s two, `foldZone`'s one, `utcZone`'s none),
instants as `Nat` literals, no text parsed. -/

section DayWitnesses

/-- UTC: no transitions. -/
def utcZone : Cal.Tz := ⟨⟨['U', 'T', 'C'], ⟨false, 0⟩, []⟩, by decide⟩

/-- **`day_index_wake_to_wake`, ported** (§6.2, inventory §2.3): Chicago, wakes at 2026-09-07T06:05-05:00
and 2026-09-08T06:40-05:00, both kept.  The first wake is on the 7th; 00:30 the next morning, before
the next wake, is the 7th; 06:20 on the 8th is the 8th (the wake is 24 h 15 min old, stale); the second
wake is the 8th; 00:30 on the 9th is the 8th; 07:00 on the 9th is the 9th (no wake that date); 05:00
on the 7th is the 7th (before the first wake).  With no wakes, 00:30 on the 8th is the 8th, and
`2026-09-08T03:00:00+00:00` is the 7th: the date is read in the zone, not the written offset.  Days
739865–739867 are 2026-09-07 to 09 (`Cal.toDay`). -/
theorem day_index_wake_to_wake_ported :
    let kw := keptWakes Cal.chicago [⟨63924375900, 0⟩, ⟨63924464400, 0⟩]
    kw = [⟨63924375900, 0⟩, ⟨63924464400, 0⟩] ∧
    dayOf Cal.chicago kw ⟨63924375900, 0⟩ = 739865 ∧
    dayOf Cal.chicago kw ⟨63924442200, 0⟩ = 739865 ∧
    dayOf Cal.chicago kw ⟨63924463200, 0⟩ = 739866 ∧
    dayOf Cal.chicago kw ⟨63924464400, 0⟩ = 739866 ∧
    dayOf Cal.chicago kw ⟨63924528600, 0⟩ = 739866 ∧
    dayOf Cal.chicago kw ⟨63924552000, 0⟩ = 739867 ∧
    dayOf Cal.chicago kw ⟨63924372000, 0⟩ = 739865 ∧
    dayOf Cal.chicago [] ⟨63924442200, 0⟩ = 739866 ∧
    dayOf Cal.chicago [] ⟨63924433200, 0⟩ = 739865 := by
  decide


/-- A wake entry of the witnesses, written at `-05:00`. -/
def wWake (line : Nat) (t : Cal.VInstant) : Entry := ⟨line, t, Log.cdt, .wake ⟨420, by decide⟩ none⟩

def wNote (line : Nat) (t : Cal.VInstant) : Entry := ⟨line, t, Log.cdt, .note ['n']⟩

/-- **Quirk Q6(a): two "first wake" rules** (gap 82).  Two wakes on 2026-09-07 in Chicago, appended out
of time order: 07:00 on line 1, then 06:05 on line 2.  The day index keeps the earlier **by instant**,
06:05; the first wake **in file order** attributed to that day is line 1's 07:00, which is what fork
`DayReplay.wake` and `slept_by_day` read.  Both rules are ported; this is what separates them. -/
theorem the_kept_wake_is_not_the_first_logged_wake :
    ∃ (z : Cal.Tz) (es : List Entry) (d : Nat) (w : Cal.Instant) (e : Entry),
      keptWakeOn z (dayIndexOf z es) d = some w ∧
      firstLoggedWakeOn z (dayIndexOf z es) (survivors es) d = some e ∧ e.t.val ≠ w :=
  ⟨Cal.chicago, [wWake 1 ⟨⟨63924379200, 0⟩, by decide⟩, wWake 2 ⟨⟨63924375900, 0⟩, by decide⟩], 739865,
    ⟨63924375900, 0⟩, wWake 1 ⟨⟨63924379200, 0⟩, by decide⟩, by decide, by decide, by decide⟩

/-- A zone whose clock falls back across midnight: UTC until 2026-09-08T00:30:00Z, `-01:00` from then
(the local clock goes from 00:30 on the 8th back to 23:30 on the 7th).  One transition. -/
def foldZone : Cal.Tz := ⟨⟨['F', 'o', 'l', 'd'], ⟨false, 0⟩, [(⟨63924424200, 0⟩, ⟨true, 3600⟩)]⟩, by decide⟩

/-- **The porting trap of §6.2: `dedup_by` is consecutive.**  In `foldZone`, wakes at 21:30 on the 7th,
00:29:59 on the 8th and, one second later, 23:30 on the 7th again have local dates 7, 8, 7 in instant
order.  The index keeps all three, since no two consecutive ones share a date, where "the earliest
wake per date" would keep two; and 23:45 on the 7th then belongs to the third wake's day, the 7th,
where the earliest-per-date index would put it on the 8th. -/
theorem the_day_index_dedups_runs_not_dates :
    keptWakes foldZone [⟨63924413400, 0⟩, ⟨63924424199, 0⟩, ⟨63924424200, 0⟩]
      = [⟨63924413400, 0⟩, ⟨63924424199, 0⟩, ⟨63924424200, 0⟩] ∧
    (([⟨63924413400, 0⟩, ⟨63924424199, 0⟩, ⟨63924424200, 0⟩] : List Cal.Instant).map (Cal.localDate foldZone))
      = [739865, 739866, 739865] ∧
    dayOf foldZone [⟨63924413400, 0⟩, ⟨63924424199, 0⟩, ⟨63924424200, 0⟩] ⟨63924425100, 0⟩ = 739865 ∧
    dayOf foldZone [⟨63924413400, 0⟩, ⟨63924424199, 0⟩] ⟨63924425100, 0⟩ = 739866 := by
  decide

/-- **Refuted as §15 wrote it** (carried note 1): with the 24-hour test on `Instant.nanos`,
`dayOf_is_the_wake_date_within_a_day` is false of the fork's day.  A wake at `03:00:59` plus 1.5 s of
leap nanoseconds on 2026-09-07 UTC and `03:01:00` on the 8th are 23 h 59 min 59.5 s apart by nanosecond
counts, and 24 h 0.5 s apart by chrono's `signed_duration_since`, which counts the leap second because
the later clock is past it in the day.  The fork gives the 8th. -/
theorem dayOf_is_the_wake_date_within_a_day_by_nanos_is_refuted :
    ∃ (kw : List Cal.Instant) (t w : Cal.Instant), lastWakeLe kw t = some w ∧
      t.nanos < w.nanos + 86400 * 1000000000 ∧ dayOf utcZone kw t ≠ Cal.localDate utcZone w :=
  ⟨[⟨63924346859, 1500000000⟩], ⟨63924433260, 0⟩, ⟨63924346859, 1500000000⟩, by decide⟩

/-- **Refuted as §15 wrote it** (carried note 1): `a_wake_day_is_shorter_than_a_day` with a nanosecond
conclusion is false of the fork's day.  A wake at 03:00:00 UTC on 2026-09-07 and the stamp
`2026-09-08T02:59:60.5Z` (second 59 with 1.5 s of leap nanoseconds, chrono's reading of `:60`): chrono
counts no leap second before a clock earlier in the day, so 23 h 59 min 59.5 s passed and the stamp is
on the wake's day, the 7th, a date not its own; by nanosecond counts 24 h 0.5 s passed. -/
theorem a_wake_day_is_shorter_than_a_day_by_nanos_is_refuted :
    ∃ (ws : List Cal.Instant) (t w : Cal.Instant),
      lastWakeLe (keptWakes utcZone ws) t = some w ∧
      dayOf utcZone (keptWakes utcZone ws) t = Cal.localDate utcZone w ∧
      Cal.localDate utcZone t ≠ Cal.localDate utcZone w ∧
      Cal.durationBetween w t = (86399, 500000000) ∧
      ¬ t.nanos < w.nanos + 86400 * 1000000000 :=
  ⟨[⟨63924346800, 0⟩], ⟨63924433199, 1500000000⟩, ⟨63924346800, 0⟩, by decide⟩

/-- **Refuted as §15 wrote it** (carried note 1): `keptWakes_append_of_later` with its hypothesis on
`Instant.nanos` is false of the fork's index, which sorts in chrono's order.  `00:01:00` has fewer
nanoseconds than `00:00:59` plus 1.5 s of leap nanoseconds and is after it in chrono's order, so the
sort puts the leap second first and the date's run keeps it, not `00:01:00`. -/
theorem keptWakes_append_of_later_by_nanos_is_refuted :
    ∃ (ws₁ ws₂ : List Cal.Instant), (∀ a ∈ ws₁, ∀ b ∈ ws₂, a.nanos < b.nanos) ∧
      keptWakes utcZone (ws₁ ++ ws₂)
        ≠ keptWakes utcZone ws₁ ++ keptFrom utcZone (keptWakes utcZone ws₁).getLast? ws₂ :=
  ⟨[⟨60, 0⟩], [⟨59, 1500000000⟩], by decide⟩

/-- **`a_wake_day_is_shorter_than_a_day`'s hypotheses are satisfiable**: 00:30 on 2026-09-08 in Chicago
belongs to the 06:05 wake of the 7th, a date not its own. -/
theorem a_wake_day_is_shorter_than_a_day_is_not_vacuous :
    lastWakeLe (keptWakes Cal.chicago [⟨63924375900, 0⟩, ⟨63924464400, 0⟩]) ⟨63924442200, 0⟩
      = some ⟨63924375900, 0⟩ ∧
    dayOf Cal.chicago (keptWakes Cal.chicago [⟨63924375900, 0⟩, ⟨63924464400, 0⟩]) ⟨63924442200, 0⟩
      = Cal.localDate Cal.chicago ⟨63924375900, 0⟩ ∧
    Cal.localDate Cal.chicago ⟨63924442200, 0⟩ ≠ Cal.localDate Cal.chicago ⟨63924375900, 0⟩ := by
  decide

/-- **An undone wake indexes nothing, and every entry keeps a day**: a wake at 06:05 on the 7th, a note
at 00:30 on the 8th, and `undo{of:"wake"}` at 00:31.  With the wake cancelled the note is on its own
date, the 8th; the cancelled wake and the undo still have days (their own dates). -/
theorem an_undone_wake_indexes_nothing :
    entryDays Cal.chicago [wWake 1 ⟨⟨63924375900, 0⟩, by decide⟩, wNote 2 ⟨⟨63924442200, 0⟩, by decide⟩,
      ⟨3, ⟨⟨63924442260, 0⟩, by decide⟩, Log.cdt, .undo Log.Kind.wake.tag none⟩]
      = [(1, 739865), (2, 739866), (3, 739866)] ∧
    entryDays Cal.chicago [wWake 1 ⟨⟨63924375900, 0⟩, by decide⟩, wNote 2 ⟨⟨63924442200, 0⟩, by decide⟩]
      = [(1, 739865), (2, 739865)] := by
  decide

end DayWitnesses

end Replay
end Tm
