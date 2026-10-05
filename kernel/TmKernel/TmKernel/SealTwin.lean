import TmKernel.SealLaw9
/-!
# SealTwin — the resume's compiled twins where the time goes (stage 5, D9, W4)

Design `kernel/design/stage5/stage5-D9-D10-design.md` §14.5 row W4 and §19 (K1, K23).  W5's gate failed (README
"Stage 5 D9 W5"), so W4 is required.  Profiled first, with callgrind on the committed `windowbench` scenarios (README
"Stage 5 D9 W4"):

* **the hot call** spent 76% of the kernel call in `resumedAnswer`: `canon`'s insertion (each insertion scans the ids
  inserted so far), and `aggMerged`'s per-id `findItem` over the checkpoint's items and per-id filter of every done
  date; quadratic in the item ids;
* **a genesis chunk** spent 82% in the fold point's scan, whose cut check recomputes `floorOf` (a day-index lookup per
  survivor) for every candidate cut, and 53% of it in `Cal.offsetAt`, a `foldl` over the zone's transitions (about 470
  for America/Chicago over 1900–2200), under `Replay.dayOf`'s `foldl` over the kept wakes.

**Every twin is a proved equality to the list specification behind `@[csimp]`** (the stage-4 `planWf` hardening pattern,
`Fast.lean`): the kernel and every law still read the specification; the compiled code is the twin.

* **Canonical lists** (`canonDesc`): `canon lt l` depends only on `l`'s elements (`canon_eq_of_mem_iff`), so it is `canon`
  over `l` merge-sorted and reversed, where each insertion stops at the head: `n log n` comparisons.  `canon` itself
  cannot be a `csimp` target (the equality needs a strict total order), so each definition over one of the checkpoint's
  four orders gets its twin (`itemIds`, `dayKeys`, `winKeys`, `windowOf`, `instOtherOf`, `namedOf`, `storedSlept`,
  `mergeTagLines`), and the four groupings compiled before them in `Seal.lean` get word-for-word twins.
* **The item tables** (`itemTables`): the checkpoint's items by id (the first of an id, as `findItem`), the done dates'
  least day and count per id, and the count of window records naming an id, each built in one pass into a bucketed map
  (`HMap`, read through `HMap.get_alter` on every map, so the bucket count never matters).  `mergedItems` (the resumed
  and resealed item list) and `resumedAnswer` are compiled over them.
* **The day index** (`dayFn`): `Replay.dayOf` over an ascending index is two bisections, the kept wakes' (C2's
  `lastWakeLeArr`) and the zone's transitions' (`offsetAtArr`, by `tz_transitions_strictly_increase`); an index that is
  not ascending (no resume builds one: `keptWakes_sorted`) reads the specification.

**Design disagreement** (recorded in the README block): the W4 row names `Std.TreeMap` twins of the item and window maps.
Since C3 those maps are bucketed hash maps (`HMap`), and the profile put the time in sorting and per-id scans of lists,
not in map lookups; so the twins are a merge sort and one-pass tables into the existing `HMap`, with no new import.

D9-21: `canonDesc` is core `mergeSort` (compiled as `mergeSortTR₂`), `reverse` and `canon`'s `foldl`, whose insertion
returns at the head on a descending list; `firstStep`, `doneIdStep`, `winStep` and `incr` are `foldl`s of one
`HMap.alter`; `bisect` recurses on halves (depth `log₂` of the array); `instAscending` is a tail call.
-/
namespace Tm
namespace Seal

open Replay (State HMap HeaderRec)

/-- `canon` over the list sorted descending: each insertion stops at the head. -/
def canonDesc {α : Type} (lt : α → α → Bool) (l : List α) : List α :=
  canon lt (l.mergeSort (fun a b => !lt b a)).reverse

theorem canon_eq_canonDesc {α : Type} {lt : α → α → Bool} (h : StrictTotal lt) (l : List α) :
    canon lt l = canonDesc lt l :=
  canon_eq_of_mem_iff h _ _ (fun y => by rw [List.mem_reverse, (List.mergeSort_perm l _).mem_iff])

def itemIdsFast (st : State) : List Log.Id :=
  canonDesc idLt (st.items.pairs.map Prod.fst ++ st.lastDone.pairs.map Prod.fst ++ st.dropped.pairs.map Prod.fst
    ++ st.doneDates.pairs.map (·.1.2))

@[csimp] theorem itemIds_eq_itemIdsFast : @itemIds = @itemIdsFast := by
  funext st; exact canon_eq_canonDesc idLt_strictTotal _

def dayKeysFast (st : State) (hs : List (Nat × HeaderRec)) : List Nat :=
  canonDesc natLt (st.days.pairs.map Prod.fst ++ st.seams.pairs.map Prod.fst ++ st.energy.map (·.day)
    ++ st.durations.map (·.day) ++ st.interrupts.map (·.day) ++ st.demotions.map Prod.fst ++ st.closes.map Prod.fst
    ++ hs.map Prod.fst ++ ((st.machine.block.bind (·.obs)).map (·.day)).toList)

@[csimp] theorem dayKeys_eq_dayKeysFast : @dayKeys = @dayKeysFast := by
  funext st hs; exact canon_eq_canonDesc natLt_strictTotal _

def winKeysFast (st : State) : List Nat :=
  canonDesc natLt (st.itemDays.pairs.map (·.1.1) ++ st.doneDates.pairs.map (·.1.1)
    ++ st.instances.pairs.filterMap (fun p => Log.instDate? p.1.2))

@[csimp] theorem winKeys_eq_winKeysFast : @winKeys = @winKeysFast := by
  funext st; exact canon_eq_canonDesc natLt_strictTotal _

def windowOfFast (st : State) (d : Nat) : WindowRecord :=
  ⟨d, (canonDesc idLt ((st.itemDays.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2))).filterMap
        (fun i => (st.itemDays.get (d, i)).map (fun m => (i, m))),
   canonDesc idLt ((st.doneDates.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2)),
   (canonDesc instKeyLt ((st.instances.pairs.filter (fun p => decide (Log.instDate? p.1.2 = some d))).map Prod.fst)).filterMap
        (fun key => (st.instances.get key).map (fun r => (key, r)))⟩

@[csimp] theorem windowOf_eq_windowOfFast : @windowOf = @windowOfFast := by
  funext st d
  simp only [windowOf, windowOfFast, ← canon_eq_canonDesc idLt_strictTotal, ← canon_eq_canonDesc instKeyLt_strictTotal]

def instOtherOfFast (st : State) : List ((List Char × List Char) × Replay.InstRec) :=
  (canonDesc instKeyLt ((st.instances.pairs.filter (fun p => (Log.instDate? p.1.2).isNone)).map Prod.fst)).filterMap
    (fun key => (st.instances.get key).map (fun r => (key, r)))

@[csimp] theorem instOtherOf_eq_instOtherOfFast : @instOtherOf = @instOtherOfFast := by
  funext st; simp only [instOtherOf, instOtherOfFast, ← canon_eq_canonDesc instKeyLt_strictTotal]

def namedOfFast (st : State) : List ((List Char × Option Log.Id) × Replay.NamedRec) :=
  (canonDesc namedKeyLt (st.named.pairs.map Prod.fst)).filterMap (fun key => (st.named.get key).map (fun r => (key, r)))

@[csimp] theorem namedOf_eq_namedOfFast : @namedOf = @namedOfFast := by
  funext st; simp only [namedOf, namedOfFast, ← canon_eq_canonDesc namedKeyLt_strictTotal]

def storedSleptFast (sl : List (Nat × Nat)) (L : Nat) : List (Nat × Nat) :=
  ((canonDesc natLt (sl.map Prod.fst)).filter (fun d => decide (L ≤ d))).filterMap
    (fun d => (Replay.KMap.get sl d).map (fun m => (d, m)))

@[csimp] theorem storedSlept_eq_storedSleptFast : @storedSlept = @storedSleptFast := by
  funext sl L; simp only [storedSlept, storedSleptFast, ← canon_eq_canonDesc natLt_strictTotal]

def mergeTagLinesFast (old new : List (List Char × Nat)) : List (List Char × Nat) :=
  (canonDesc idLt (old.map Prod.fst ++ new.map Prod.fst)).map (fun t =>
    (t, ((new.find? (fun p => p.1 == t)).map Prod.snd).getD (((old.find? (fun p => p.1 == t)).map Prod.snd).getD 0)))

@[csimp] theorem mergeTagLines_eq_mergeTagLinesFast : @mergeTagLines = @mergeTagLinesFast := by
  funext old new; simp only [mergeTagLines, mergeTagLinesFast, ← canon_eq_canonDesc idLt_strictTotal]

/-! Word-for-word twins, compiled after the csimps above. -/
def daysInT (st : State) (hs : List (Nat × HeaderRec)) (lo hi : Nat) : List OpenDay :=
  ((dayKeys st hs).filter (fun d => decide (lo ≤ d ∧ d < hi))).map (openDayOf st hs)
@[csimp] theorem daysIn_eq_daysInT : @daysIn = @daysInT := rfl
def daysFromT (st : State) (hs : List (Nat × HeaderRec)) (lo : Nat) : List OpenDay :=
  ((dayKeys st hs).filter (fun d => decide (lo ≤ d))).map (openDayOf st hs)
@[csimp] theorem daysFrom_eq_daysFromT : @daysFrom = @daysFromT := rfl
/-! ## The window facts, grouped by date once (each record read from its date's group, not a filter of every pair) -/


/-- One pair grouped under its date, if it names one. -/
def groupStep {π γ : Type} (key : π → Option Nat) (val : π → γ) (m : HMap Nat (List γ)) (p : π) : HMap Nat (List γ) :=
  match key p with
  | some d => m.alter d (fun o => some (val p :: o.getD []))
  | none => m

theorem mem_foldl_groupStep {π γ : Type} (key : π → Option Nat) (val : π → γ) (d : Nat) (x : γ) :
    ∀ (l : List π) (m : HMap Nat (List γ)),
      x ∈ ((l.foldl (groupStep key val) m).get d).getD [] ↔ x ∈ (m.get d).getD [] ∨ ∃ p ∈ l, key p = some d ∧ val p = x
  | [], m => by simp
  | p :: l, m => by
    rw [List.foldl_cons, mem_foldl_groupStep key val d x l]
    have hcons : (∃ q ∈ p :: l, key q = some d ∧ val q = x)
        ↔ (key p = some d ∧ val p = x) ∨ ∃ q ∈ l, key q = some d ∧ val q = x := by
      constructor
      · rintro ⟨q, hq, h⟩
        rcases List.mem_cons.1 hq with rfl | hq
        · exact Or.inl h
        · exact Or.inr ⟨q, hq, h⟩
      · rintro (h | ⟨q, hq, h⟩)
        · exact ⟨p, List.mem_cons_self, h⟩
        · exact ⟨q, List.mem_cons_of_mem _ hq, h⟩
    rw [hcons]
    unfold groupStep
    split
    · rename_i d' hk
      rw [HMap.get_alter]
      by_cases hd : d = d'
      · subst hd
        simp only [if_true, Option.getD_some, List.mem_cons, hk, true_and]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inr (Or.inl h.symm)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h.symm)
          · exact Or.inr h
      · have hk' : ¬ key p = some d := by rw [hk]; intro h; exact hd (Option.some.inj h).symm
        simp only [hd, if_false, hk', false_and, false_or]
    · rename_i hk
      have hk' : ¬ key p = some d := by rw [hk]; simp
      simp only [hk', false_and, false_or]

/-- **The window facts grouped by date**, once. -/
structure WinGroups where
  itemDays : HMap Nat (List Log.Id)
  doneDates : HMap Nat (List Log.Id)
  inst : HMap Nat (List (List Char × List Char))

def winGroups (st : State) : WinGroups :=
  let a := st.itemDays.pairs
  let b := st.doneDates.pairs
  let c := st.instances.pairs
  ⟨a.foldl (groupStep (fun p => some p.1.1) (fun p => p.1.2)) (HMap.empty a.length),
   b.foldl (groupStep (fun p => some p.1.1) (fun p => p.1.2)) (HMap.empty b.length),
   c.foldl (groupStep (fun p => Log.instDate? p.1.2) Prod.fst) (HMap.empty c.length)⟩

def windowOfG (g : WinGroups) (st : State) (d : Nat) : WindowRecord :=
  ⟨d, (canonDesc idLt ((g.itemDays.get d).getD [])).filterMap (fun i => (st.itemDays.get (d, i)).map (fun m => (i, m))),
   canonDesc idLt ((g.doneDates.get d).getD []),
   (canonDesc instKeyLt ((g.inst.get d).getD [])).filterMap (fun key => (st.instances.get key).map (fun r => (key, r)))⟩

theorem windowOfG_eq (st : State) (d : Nat) : windowOfG (winGroups st) st d = windowOf st d := by
  have h1 : ∀ i, i ∈ ((winGroups st).itemDays.get d).getD [] ↔
      i ∈ (st.itemDays.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2) := by
    intro i
    simp only [winGroups, mem_foldl_groupStep, HMap.get_empty, Option.getD_none, List.not_mem_nil, false_or,
      Option.some.injEq, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨p, h, h'⟩; exact ⟨p, ⟨h, h'.1⟩, h'.2⟩
    · rintro ⟨p, h, h'⟩; exact ⟨p, h.1, h.2, h'⟩
  have h2 : ∀ i, i ∈ ((winGroups st).doneDates.get d).getD [] ↔
      i ∈ (st.doneDates.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2) := by
    intro i
    simp only [winGroups, mem_foldl_groupStep, HMap.get_empty, Option.getD_none, List.not_mem_nil, false_or,
      Option.some.injEq, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨p, h, h'⟩; exact ⟨p, ⟨h, h'.1⟩, h'.2⟩
    · rintro ⟨p, h, h'⟩; exact ⟨p, h.1, h.2, h'⟩
  have h3 : ∀ k, k ∈ ((winGroups st).inst.get d).getD [] ↔
      k ∈ (st.instances.pairs.filter (fun p => decide (Log.instDate? p.1.2 = some d))).map Prod.fst := by
    intro k
    simp only [winGroups, mem_foldl_groupStep, HMap.get_empty, Option.getD_none, List.not_mem_nil, false_or,
      List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨p, h, h'⟩; exact ⟨p, ⟨h, h'.1⟩, h'.2⟩
    · rintro ⟨p, h, h'⟩; exact ⟨p, h.1, h.2, h'⟩
  simp only [windowOfG, windowOf, ← canon_eq_canonDesc idLt_strictTotal, ← canon_eq_canonDesc instKeyLt_strictTotal]
  rw [canon_eq_of_mem_iff idLt_strictTotal _ _ h1, canon_eq_of_mem_iff idLt_strictTotal _ _ h2,
    canon_eq_of_mem_iff instKeyLt_strictTotal _ _ h3]

def windowsInG (st : State) (lo hi : Nat) : List WindowRecord :=
  let g := winGroups st
  ((winKeys st).filter (fun d => decide (lo ≤ d ∧ d < hi))).map (windowOfG g st)

/-- **The window records of a range are read from the groups** (`@[csimp]`). -/
@[csimp] theorem windowsIn_eq_windowsInG : @windowsIn = @windowsInG := by
  funext st lo hi
  have hf : windowOfG (winGroups st) st = windowOf st := funext (windowOfG_eq st)
  simp only [windowsIn, windowsInG, hf]

def windowsFromG (st : State) (lo : Nat) : List WindowRecord :=
  let g := winGroups st
  ((winKeys st).filter (fun d => decide (lo ≤ d))).map (windowOfG g st)

/-- **The window records from a date are read from the groups** (`@[csimp]`). -/
@[csimp] theorem windowsFrom_eq_windowsFromG : @windowsFrom = @windowsFromG := by
  funext st lo
  have hf : windowOfG (winGroups st) st = windowOf st := funext (windowOfG_eq st)
  simp only [windowsFrom, windowsFromG, hf]

/-! ## The item tables -/

def firstStep (m : HMap Log.Id ItemAgg) (a : ItemAgg) : HMap Log.Id ItemAgg := m.alter a.id (fun o => o.or (some a))

theorem foldl_firstStep_get (i : Log.Id) : ∀ (l : List ItemAgg) (m : HMap Log.Id ItemAgg),
    (l.foldl firstStep m).get i = (m.get i).or (findItem l i)
  | [], m => by simp [findItem]
  | a :: l, m => by
    rw [List.foldl_cons, foldl_firstStep_get i l, firstStep, HMap.get_alter]
    unfold findItem
    rw [List.find?_cons]
    by_cases h : i = a.id
    · subst h; cases m.get a.id <;> simp
    · have h' : ¬ a.id = i := fun e => h e.symm
      simp [h, h']

def doneStep (acc : Option Nat × Nat) (d : Nat) : Option Nat × Nat :=
  (some (match acc.1 with | none => d | some a => Nat.min a d), acc.2 + 1)

theorem foldl_doneStep : ∀ (l : List Nat) (a : Option Nat) (c : Nat),
    l.foldl doneStep (a, c) = (l.foldl (fun acc d => some (match acc with | none => d | some a => Nat.min a d)) a, c + l.length)
  | [], a, c => by simp
  | d :: l, a, c => by
    rw [List.foldl_cons, List.foldl_cons]
    simp only [doneStep]
    rw [foldl_doneStep l]
    simp only [List.length_cons, Prod.mk.injEq, true_and]
    omega

def doneIdStep (m : HMap Log.Id (Option Nat × Nat)) (p : (Nat × Log.Id) × Unit) : HMap Log.Id (Option Nat × Nat) :=
  m.alter p.1.2 (fun o => some (doneStep (o.getD (none, 0)) p.1.1))

theorem foldl_doneIdStep_get (i : Log.Id) : ∀ (l : List ((Nat × Log.Id) × Unit)) (m : HMap Log.Id (Option Nat × Nat)),
    ((l.foldl doneIdStep m).get i).getD (none, 0) =
      ((l.filter (fun p => decide (p.1.2 = i))).map (·.1.1)).foldl doneStep ((m.get i).getD (none, 0))
  | [], m => rfl
  | ⟨⟨d, i'⟩, u⟩ :: l, m => by
    rw [List.foldl_cons, foldl_doneIdStep_get i l, doneIdStep, HMap.get_alter, List.filter_cons]
    by_cases h : i' = i
    · subst h; simp
    · have h' : ¬ i = i' := fun e => h e.symm
      simp [h, h']

def incr (m : HMap Log.Id Nat) (i : Log.Id) : HMap Log.Id Nat := m.alter i (fun o => some (o.getD 0 + 1))

theorem foldl_incr_get (i : Log.Id) : ∀ (l : List Log.Id) (m : HMap Log.Id Nat), l.Nodup →
    ((l.foldl incr m).get i).getD 0 = (m.get i).getD 0 + (if i ∈ l then 1 else 0)
  | [], m, _ => by simp
  | x :: l, m, hn => by
    rw [List.foldl_cons, foldl_incr_get i l _ (List.nodup_cons.1 hn).2, incr, HMap.get_alter]
    by_cases h : i = x
    · subst h
      have := (List.nodup_cons.1 hn).1
      simp [this]
    · simp [h]

def winStep (m : HMap Log.Id Nat) (w : WindowRecord) : HMap Log.Id Nat := (canonDesc idLt w.doneIds).foldl incr m

theorem foldl_winStep_get (i : Log.Id) : ∀ (ws : List WindowRecord) (m : HMap Log.Id Nat),
    ((ws.foldl winStep m).get i).getD 0 = (m.get i).getD 0 + (ws.filter (fun w => w.doneIds.contains i)).length
  | [], m => by simp
  | w :: ws, m => by
    have hn : (canonDesc idLt w.doneIds).Nodup := by
      rw [← canon_eq_canonDesc idLt_strictTotal]; exact nodup_canon idLt_strictTotal _
    have hm : (i ∈ canonDesc idLt w.doneIds) ↔ w.doneIds.contains i = true := by
      rw [← canon_eq_canonDesc idLt_strictTotal, mem_canon idLt_strictTotal]; simp
    rw [List.foldl_cons, foldl_winStep_get i ws, winStep, foldl_incr_get i _ _ hn, List.filter_cons]
    by_cases h : w.doneIds.contains i = true
    · simp only [hm.2 h, if_true, h, List.length_cons]; omega
    · simp only [(not_congr hm).2 h, if_false, h, Bool.false_eq_true]; omega

structure ItemTables where
  old : HMap Log.Id ItemAgg
  done : HMap Log.Id (Option Nat × Nat)
  win : HMap Log.Id Nat

def itemTables (K : Ckpt) (st : State) : ItemTables :=
  ⟨K.items.foldl firstStep (HMap.empty K.items.length),
   st.doneDates.pairs.foldl doneIdStep (HMap.empty K.items.length),
   K.window.foldl winStep (HMap.empty K.window.length)⟩

def aggMergedT (t : ItemTables) (_K : Ckpt) (st : State) (i : Log.Id) : ItemAgg :=
  let old := t.old.get i
  let dd := (t.done.get i).getD (none, 0)
  ⟨i, st.items.get i, st.lastDone.get i, (st.dropped.get i).isSome, minOpt (old.bind (·.doneFirst)) dd.1,
   ((old.map (·.doneCount)).getD 0) - (t.win.get i).getD 0 + dd.2⟩

theorem aggMergedT_eq (K : Ckpt) (st : State) (i : Log.Id) : aggMergedT (itemTables K st) K st i = aggMerged K st i := by
  have h1 := foldl_firstStep_get i K.items (HMap.empty K.items.length)
  have h2 := foldl_doneIdStep_get i st.doneDates.pairs (HMap.empty K.items.length)
  have h3 := foldl_winStep_get i K.window (HMap.empty K.window.length)
  rw [HMap.get_empty] at h1 h2 h3
  simp only [Option.none_or, Option.getD_none, Nat.zero_add] at h1 h2 h3
  rw [foldl_doneStep] at h2
  simp only [aggMergedT, aggMerged, itemTables, h1, h2, h3, Replay.minDay?, Nat.zero_add]
  rfl

def mergedItems (K : Ckpt) (st : State) : List ItemAgg := (canon idLt (K.items.map (·.id) ++ itemIds st)).map (aggMerged K st)

def mergedItemsFast (K : Ckpt) (st : State) : List ItemAgg :=
  (canonDesc idLt (K.items.map (·.id) ++ (st.items.pairs.map Prod.fst ++ st.lastDone.pairs.map Prod.fst
    ++ st.dropped.pairs.map Prod.fst ++ st.doneDates.pairs.map (·.1.2)))).map (aggMergedT (itemTables K st) K st)

@[csimp] theorem mergedItems_eq_mergedItemsFast : @mergedItems = @mergedItemsFast := by
  funext K st
  have hf : aggMergedT (itemTables K st) K st = aggMerged K st := funext (aggMergedT_eq K st)
  simp only [mergedItems, mergedItemsFast, hf]
  congr 1
  rw [← canon_eq_canonDesc idLt_strictTotal]
  apply canon_eq_of_mem_iff idLt_strictTotal
  intro y
  simp only [List.mem_append, itemIds, mem_canon idLt_strictTotal]

def resumedAnswerFast (K : Ckpt) (st : State) (hs : List (Nat × HeaderRec)) (entries : Nat) (ws : List (Nat × Log.LWarn)) :
    Seal.Answer :=
  ⟨K.ledgerDay, horizonOf K.ledgerDay,
   (mergedItemsFast K st).map ItemAgg.finish,
   windowsFrom st (horizonOf K.ledgerDay), instOtherOf st, namedOf st,
   (daysFrom st hs K.ledgerDay).map (OpenDay.finish st.machine),
   Replay.openOf st.machine,
   st.machine.interrupt.map (fun i => ⟨0, some i.1, none, i.2.1, i.2.2, 0, []⟩),
   st.machine.brkOpen,
   maxOpt K.lastDay (Replay.maxDay? (st.days.pairs.map Prod.fst)),
   st.global.lastEffective, K.entryCount + entries, st.unknown, st.longestLeak, st.rwarns.reverse,
   (K.warnings ++ ws).take maxWarnings, K.warnings.length + K.warnOverflow + ws.length - maxWarnings⟩

@[csimp] theorem resumedAnswer_eq_resumedAnswerFast : @resumedAnswer = @resumedAnswerFast := by
  funext K st hs entries ws
  simp only [resumedAnswer, resumedAnswerFast]
  rw [← mergedItems_eq_mergedItemsFast]
  simp only [mergedItems, List.map_map]
  rfl

/-- **The compiled resume reads its open block through `Replay.openOf`** (D94, README gap 4361): the twin the binary
runs hands the planner the block the machine holds read past every break held ahead of its clock, as `Seal.answer` and
`Replay.finish` do — stated of the twin itself, so the twin is told from a constant by more than the `@[csimp]` lemma's
one proof (D40; the W-44 track K mutation of `resumedAnswerFast` read ALONE without it). -/
theorem the_compiled_resume_reads_its_open_block_through_openOf (K : Ckpt) (st : State) (hs : List (Nat × HeaderRec))
    (entries : Nat) (ws : List (Nat × Log.LWarn)) :
    (resumedAnswerFast K st hs entries ws).openBlock = Replay.openOf st.machine := rfl

/-! ## The day index, by bisection -/

/-- **A bisection over an array**: the first index of `[lo, hi)` whose element fails `P`, for a `P` that holds on a
prefix. -/
def bisect {α : Type} (a : Array α) (P : α → Bool) (lo hi : Nat) : Nat :=
  if _h : lo < hi then
    match a[(lo + hi) / 2]? with
    | some x => if P x then bisect a P ((lo + hi) / 2 + 1) hi else bisect a P lo ((lo + hi) / 2)
    | none => lo
  else lo
termination_by hi - lo
decreasing_by all_goals omega

theorem bisect_spec {α : Type} (l : List α) (P : α → Bool) (hs : l.Pairwise (fun x y => P y = true → P x = true))
    (lo hi : Nat) (hlh : lo ≤ hi) (hn : hi ≤ l.length)
    (hlo : ∀ i (hi' : i < l.length), i < lo → P l[i] = true)
    (hhi : ∀ i (hi' : i < l.length), hi ≤ i → P l[i] = false) :
    bisect l.toArray P lo hi ≤ l.length ∧
    (∀ i (h : i < l.length), i < bisect l.toArray P lo hi → P l[i] = true) ∧
    (∀ i (h : i < l.length), bisect l.toArray P lo hi ≤ i → P l[i] = false) := by
  rw [bisect]
  split
  · rename_i h
    have hm : (lo + hi) / 2 < l.length := by omega
    rw [List.getElem?_toArray, List.getElem?_eq_getElem hm]
    simp only
    split
    · rename_i hp
      apply bisect_spec l P hs _ hi (by omega) hn
      · intro i hi' hi2
        by_cases hlt : i < lo
        · exact hlo i hi' hlt
        · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi2) with hi3 | hi3
          · exact List.pairwise_iff_getElem.1 hs i _ hi' hm hi3 hp
          · simp only [hi3]; exact hp
      · exact hhi
    · rename_i hp
      apply bisect_spec l P hs lo _ (by omega) (by omega) hlo
      intro i hi' hi2
      rcases Nat.lt_or_eq_of_le hi2 with hi3 | hi3
      · cases hc : P l[i] with
        | false => rfl
        | true => exact absurd (List.pairwise_iff_getElem.1 hs _ i hm hi' hi3 hc) hp
      · simp only [← hi3]; simpa using hp
  · refine ⟨by omega, fun i hi' hi2 => hlo i hi' hi2, fun i hi' hi2 => hhi i hi' (by omega)⟩
termination_by hi - lo
decreasing_by all_goals omega

/-- A fold keeping the last element that passes a prefix test is read at the prefix's end. -/
theorem foldl_last_of_point {α β : Type} (P : α → Bool) (f : α → β) : ∀ (l : List α) (b : β) (p : Nat), p ≤ l.length →
    (∀ i (h : i < l.length), i < p → P l[i] = true) →
    (∀ i (h : i < l.length), p ≤ i → P l[i] = false) →
    l.foldl (fun acc x => if P x = true then f x else acc) b = (match p with | 0 => b | q + 1 => (l[q]?.map f).getD b)
  | [], b, p, hp, _, _ => by simp at hp; subst hp; rfl
  | x :: xs, b, 0, _, _, h2 => by
    have hx : P x = false := by have := h2 0 (by simp) (Nat.le_refl 0); simpa using this
    rw [List.foldl_cons, if_neg (by simp [hx])]
    exact foldl_last_of_point P f xs b 0 (Nat.zero_le _) (fun i _ hi => absurd hi (Nat.not_lt_zero _))
      (fun i h _ => by have := h2 (i + 1) (by simp; omega) (Nat.zero_le _); simpa using this)
  | x :: xs, b, q + 1, hp, h1, h2 => by
    have hx : P x = true := by have := h1 0 (by simp) (Nat.succ_pos _); simpa using this
    rw [List.foldl_cons, if_pos hx]
    rw [foldl_last_of_point P f xs (f x) q (by simp at hp; omega)
      (fun i h hi => by have := h1 (i + 1) (by simp; omega) (by omega); simpa using this)
      (fun i h hi => by have := h2 (i + 1) (by simp; omega) (by omega); simpa using this)]
    cases q with
    | zero => simp
    | succ r =>
      have hr : r < xs.length := by simp at hp; omega
      simp [List.getElem?_eq_getElem hr]

/-- **The offset in force, by bisection** over the transitions as an array. -/
def offsetAtArr (base : Cal.Offset) (a : Array (Cal.Instant × Cal.Offset)) (t : Cal.Instant) : Cal.Offset :=
  match bisect a (fun p => decide (p.1.sec ≤ t.sec)) 0 a.size with
  | 0 => base
  | q + 1 => (a[q]?.map Prod.snd).getD base

theorem offsetAtArr_eq (z : Cal.Tz) (t : Cal.Instant) :
    offsetAtArr z.val.base z.val.trans.toArray t = Cal.offsetAt z t := by
  have hs : z.val.trans.Pairwise
      (fun x y => decide (y.1.sec ≤ t.sec) = true → decide (x.1.sec ≤ t.sec) = true) :=
    (Cal.tz_transitions_strictly_increase z).imp (fun {x y} hxy hy => by
      simp only [decide_eq_true_eq] at *
      rcases (Cal.Instant.lt_iff _ _).1 hxy with h | ⟨h, _⟩ <;> omega)
  obtain ⟨hp, h1, h2⟩ := bisect_spec z.val.trans _ hs 0 z.val.trans.length (Nat.zero_le _) (Nat.le_refl _)
    (fun i _ h => absurd h (Nat.not_lt_zero _)) (fun i hi h => absurd hi (Nat.not_lt.2 h))
  have hf := foldl_last_of_point (fun p : Cal.Instant × Cal.Offset => decide (p.1.sec ≤ t.sec)) Prod.snd
    z.val.trans z.val.base _ hp h1 h2
  have hstep : Cal.offsetStep t
      = (fun acc (x : Cal.Instant × Cal.Offset) => if decide (x.1.sec ≤ t.sec) = true then x.2 else acc) := by
    funext acc x; simp [Cal.offsetStep]
  unfold Cal.offsetAt
  rw [hstep, hf]
  unfold offsetAtArr
  simp only [List.size_toArray, List.getElem?_toArray]

def localDateArr (z : Cal.Tz) (a : Array (Cal.Instant × Cal.Offset)) (t : Cal.Instant) : Nat :=
  Cal.localSecAt (offsetAtArr z.val.base a t) t / 86400

theorem localDateArr_eq (z : Cal.Tz) (t : Cal.Instant) : localDateArr z z.val.trans.toArray t = Cal.localDate z t := by
  simp only [localDateArr, offsetAtArr_eq, Cal.localDate, Cal.localSec]

/-- **`dayOf` over two arrays**: the wakes' bisection and the transitions'. -/
def dayOfZ (z : Cal.Tz) (ta : Array (Cal.Instant × Cal.Offset)) (wa : Array Cal.Instant) (t : Cal.Instant) : Nat :=
  match Replay.lastWakeLeArr wa t with
  | some w => if (Cal.durationBetween w t).1 < 86400 then localDateArr z ta w else localDateArr z ta t
  | none => localDateArr z ta t

theorem dayOfZ_eq (z : Cal.Tz) (kw : List Cal.Instant) (hs : kw.Pairwise (· ≤ ·)) (t : Cal.Instant) :
    dayOfZ z z.val.trans.toArray kw.toArray t = Replay.dayOf z kw t := by
  unfold dayOfZ Replay.dayOf
  rw [Replay.lastWakeLeArr_eq_lastWakeLe _ hs]
  simp only [localDateArr_eq]
  rfl

/-- Instants in ascending order, checked (a tail call). -/
def instAscending : List Cal.Instant → Bool
  | a :: b :: rest => decide (a ≤ b) && instAscending (b :: rest)
  | _ => true

theorem instAscending_pairwise : ∀ (l : List Cal.Instant), instAscending l = true → l.Pairwise (· ≤ ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [instAscending, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := instAscending_pairwise (b :: rest) h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact Replay.instant_le_trans h.1 (List.rel_of_pairwise_cons ih hc)

/-- **The day index as a function, compiled**: the bisections when the index is ascending (every index a resume
builds is: `keptWakes_sorted`), else the specification. -/
def dayFn (z : Cal.Tz) (kw : List Cal.Instant) : Cal.Instant → Nat :=
  if instAscending kw then dayOfZ z z.val.trans.toArray kw.toArray else Replay.dayOf z kw

theorem dayFn_eq (z : Cal.Tz) (kw : List Cal.Instant) : dayFn z kw = Replay.dayOf z kw := by
  unfold dayFn
  split
  · rename_i h; funext t; exact dayOfZ_eq z kw (instAscending_pairwise kw h) t
  · rfl

end Seal
end Tm
