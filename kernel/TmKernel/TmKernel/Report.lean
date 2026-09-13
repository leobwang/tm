import TmKernel.Close
import TmKernel.Arith
/-!
# What a close reports — the owner's D3, as a named per-item list

A close rewrites files; the host needs to say *what happened to each item* —
on screen now, and to the month review later, whose cut list is "≥ 2 stamps".
The owner's decision D3 (2026-09-12): **a per-item list** — for each line the
close touched, its id, what happened to it (a *named* disposition), where it
went, which stamp it gained, and its minutes as an integer numerator /
denominator pair.  Not counts only: a month review that re-derived per-item
history from the files would be a second reader of one fact.  Not stage 6's
full diagnostics surface yet.

**One definition, not a second reader.**  An entry is not computed by watching
the fold; it is read off the same three functions the fold runs — `closeAct`
(taken or not, and how), `stepSkel` (where the line ends up, with what bytes)
and `closeStamp` (which stamp) — against the plan the close was handed.  The
theorems below tie the list to the close's *result*: every id the close acts on
is named once, in fold order (`closeReport_ids`), and under a successful close
each entry's source, destination, stamp and minutes are exactly the item's
before and after (`closeReport_agrees_with_close_stamping_or_merging`).  So the report cannot say a
line went somewhere it did not.

**AGENTS §8.2's four rules for the shape, each met here or in `Boundary.lean`:**

1. it is a value under `ok`, beside `docs` — `runPlan` builds it only on the
   success path, so a host that gets `err` gets no report;
2. every field is a bounded type with a smart constructor its decoder uses —
   `Grain` is `Fin 3`, the disposition is `CloseDid` (five constructors since
   README gap 53 added `copyMerging`, six since D7 added `moveOverdue`;
   `CloseDid.ofName?` refuses every other spelling), a stamp is `Field.Stamp`
   (whose parser is `parseStamp`), minutes are `Arith.Pos` (`den > 0`, built by
   `Arith.posOfNat`, decoded by `Arith.ofPair?`, which refuses `den = 0`), and
   the block length is `BlockMin` (`BlockMin.ofNat?` refuses `0`);
3. every entry is named — the disposition by constructor name, the way
   `kerrName` names a `KErr`;
4. minutes are an integer pair and nothing here divides — `Arith.Pos` is a
   numerator and a positive denominator; the host divides on screen.

**How stage 6 extends it without reshaping.**  `Report` is a record of named
families, and stage 4 ships one, `closes`.  Stage 6's diagnostics families and
plan segments are further fields of `Report` — each its own list of named
entries, emitted as a further key of the `report` object after `closes` — so a
reader that looks `closes` up by name is untouched, and no entry type changes.
-/
namespace Tm

open Field (Stamp)

/-! ## The bounded inputs and fields -/

/-- **The block length, in minutes** — what `Nb` means (§4.1).  Positive: a
zero-minute block would read every block estimate as nothing. -/
abbrev BlockMin := { n : Nat // 0 < n }

/-- The smart constructor the wire decoder uses. -/
def BlockMin.ofNat? (n : Nat) : Option BlockMin :=
  if h : 0 < n then some ⟨n, h⟩ else none

/-- **The check bites**: a zero block length is refused, not repaired. -/
theorem BlockMin.ofNat?_zero : BlockMin.ofNat? 0 = none := rfl

/-- **It does not over-bite**: every positive length is accepted as itself. -/
theorem BlockMin.ofNat?_pos {n : Nat} (h : 0 < n) : BlockMin.ofNat? n = some ⟨n, h⟩ := by
  simp [BlockMin.ofNat?, h]

/-- **What a close did to one line, by name.**  The first three are the
`ClosePolicy` row's `Disposition`; the fourth is the week row's copy of a line whose
item already had a `# Demoted` record, merged into it (README gap 53); the fifth is
the wall exemption's carry; the sixth is the week row's overdue route (D7). -/
inductive CloseDid
  /-- moved, unchanged (§6.3's month row) -/
  | move
  /-- moved, `[>]` reopened to `[ ]`, stamped (§6.3's day row) -/
  | moveReopening
  /-- `[-]` left behind, the stamped record filed forward (§6.3's week row) -/
  | copy
  /-- `[-]` left behind, and the item's standing `# Demoted` record rewritten in
      its place: stamps merged, estimate floored per L15 (§6.3's week row over
      §4.3's pre-close pair, fork-point `demote_one`; README gap 53) -/
  | copyMerging
  /-- a wall still ahead, moved undemoted into the live week -/
  | carry
  /-- past due with `persist`: moved undemoted, unstamped, leaving no tombstone,
      to the end of `backlog.md`'s `# Overdue` (§6.3's week row; the owner's D7) -/
  | moveOverdue
deriving DecidableEq, Repr

def CloseDid.ofDisposition : Disposition → CloseDid
  | .move          => .move
  | .moveReopening => .moveReopening
  | .copy          => .copy

/-- The name of a filing step: the row's disposition, and `copyMerging` for a copy
of a line whose item has a standing record (`merging`). -/
def CloseDid.ofStep : Disposition → Bool → CloseDid
  | .copy, true => .copyMerging
  | d,     _    => .ofDisposition d

theorem CloseDid.ofStep_ne_carry (d : Disposition) (b : Bool) : CloseDid.ofStep d b ≠ .carry := by
  cases d <;> cases b <;> simp [CloseDid.ofStep, CloseDid.ofDisposition]

theorem CloseDid.ofStep_ne_moveOverdue (d : Disposition) (b : Bool) :
    CloseDid.ofStep d b ≠ .moveOverdue := by
  cases d <;> cases b <;> simp [CloseDid.ofStep, CloseDid.ofDisposition]

/-- The name on the wire: the constructor's own. -/
def CloseDid.name : CloseDid → String
  | .move          => "move"
  | .moveReopening => "moveReopening"
  | .copy          => "copy"
  | .copyMerging   => "copyMerging"
  | .carry         => "carry"
  | .moveOverdue   => "moveOverdue"

/-- The decoder's smart constructor: exactly the six names, nothing else. -/
def CloseDid.ofName? (s : List Char) : Option CloseDid :=
  if s = "move".toList then some .move
  else if s = "moveReopening".toList then some .moveReopening
  else if s = "copy".toList then some .copy
  else if s = "copyMerging".toList then some .copyMerging
  else if s = "carry".toList then some .carry
  else if s = "moveOverdue".toList then some .moveOverdue
  else none

theorem CloseDid.ofName?_name : ∀ d : CloseDid, CloseDid.ofName? d.name.toList = some d := by
  intro d; cases d <;> decide

/-- **The decoder bites**: a near-miss spelling, a case change and the empty
string are refused. -/
theorem CloseDid.ofName?_refuses :
    CloseDid.ofName? "moved".toList = none ∧ CloseDid.ofName? "Copy".toList = none ∧
      CloseDid.ofName? "copymerging".toList = none ∧ CloseDid.ofName? [] = none := by
  decide

/-- D7's name bites too: the Rust report's `overdue_to_backlog` and a case change
are not `moveOverdue`. -/
theorem CloseDid.ofName?_refuses_near_overdue :
    CloseDid.ofName? "overdue".toList = none ∧ CloseDid.ofName? "overdue_to_backlog".toList = none ∧
      CloseDid.ofName? "moveoverdue".toList = none := by
  decide

/-- **An item's minutes**, as the kernel reads them: the estimate view
`Core.est` reads (`est:` over the leading estimate), in minutes at block length
`bm`, as a ratio with a positive denominator.  `none` is "this line carries no
estimate" — never `0`, which is an estimate. -/
def estMinutes (bm : BlockMin) (r : RawItem) : Option Arith.Pos :=
  (Field.viewRemainingDur r).map (fun d => Arith.posOfNat (d.minutes bm.val))

/-! ## The entry and the report -/

/-- **One line a close touched.**  `src` and `dst` are document indices — the
wire's own addressing, the `doc` a command names — so the host reads the path
off the response's `docs` array. -/
structure CloseEntry where
  id      : Id
  /-- the grain of the close that took it -/
  grain   : Grain
  did     : CloseDid
  /-- the closed file its live line was in -/
  src     : DocIx
  /-- the file its live line is in now -/
  dst     : DocIx
  /-- the stamp it gained, if any -/
  stamp   : Option Stamp
  /-- its estimate afterwards, in minutes -/
  minutes : Option Arith.Pos
deriving DecidableEq

/-- **What a response reports.**  One family at stage 4; stage 6 adds fields. -/
structure Report where
  closes : List CloseEntry
deriving DecidableEq

def Report.empty : Report := ⟨[]⟩

def Report.append (a b : Report) : Report := ⟨a.closes ++ b.closes⟩

/-- The entry for one line, read off the step the fold takes. -/
def closeEntry (g : Grain) (now : Day) (bm : BlockMin) (p : PlanCore) (i : Id) (s : Skel) :
    Option CloseEntry :=
  match closeAct g now p s with
  | .stay   => none
  | .carry  => some ⟨i, g, .carry, s.doc, (stepSkel g now p s).doc, none,
                     estMinutes bm (stepSkel g now p s).line⟩
  | .file r => some ⟨i, g, .ofStep (closePolicy g).disposition s.archLine.isSome, s.doc,
                     (stepSkel g now p s).doc, closeStamp g r.ix,
                     estMinutes bm (stepSkel g now p s).line⟩
  | .overdue => some ⟨i, g, .moveOverdue, s.doc, (stepSkel g now p s).doc, none,
                     estMinutes bm (stepSkel g now p s).line⟩

/-- **The report of `close g now` on plan `p`**: one entry per candidate, in the
order the fold takes them. -/
def closeReport (g : Grain) (now : Day) (bm : BlockMin) (p : PlanCore) : List CloseEntry :=
  (closeCands g now p).filterMap (fun i =>
    (p.store.get i).bind (fun e => closeEntry g now bm p i e.val.skel))

/-- `close`, reporting. -/
def closeR (g : Grain) (now : Day) (bm : BlockMin) (p : WfPlan) : Except KErr (WfPlan × Report) :=
  (close g now p).map (fun q => (q, ⟨closeReport g now bm p.val⟩))

/-- One grain of `autoClose`, reporting: the close, and its entries appended. -/
def closeStepR (now : Day) (bm : BlockMin) (acc : WfPlan × Report) (g : Grain) :
    Except KErr (WfPlan × Report) :=
  (close g now acc.1).map (fun q => (q, acc.2.append ⟨closeReport g now bm acc.1.val⟩))

/-- `autoClose`, reporting: the same fold over `autoCloseOrder`, each grain's
entries against the plan that grain's close was handed. -/
def autoCloseR (now : Day) (bm : BlockMin) (p : WfPlan) : Except KErr (WfPlan × Report) :=
  autoCloseOrder.foldlM (closeStepR now bm) (p, Report.empty)

/-! ## The reporting forms are the closes -/

theorem closeR_plan (g : Grain) (now : Day) (bm : BlockMin) (p : WfPlan) :
    (closeR g now bm p).map Prod.fst = close g now p := by
  unfold closeR
  cases close g now p <;> rfl

theorem foldlM_closeStepR_plan (now : Day) (bm : BlockMin) :
    ∀ (gs : List Grain) (p : WfPlan) (r : Report),
      (gs.foldlM (closeStepR now bm) (p, r)).map Prod.fst =
        gs.foldlM (fun q g => close g now q) p := by
  intro gs
  induction gs with
  | nil => intro p r; rfl
  | cons g rest ih =>
    intro p r
    simp only [List.foldlM_cons]
    unfold closeStepR
    cases hc : close g now p with
    | error x => rfl
    | ok q =>
      show (rest.foldlM (closeStepR now bm) (q, r.append ⟨closeReport g now bm p.val⟩)).map Prod.fst =
        rest.foldlM (fun q g => close g now q) q
      exact ih q _

/-- **`autoCloseR` is `autoClose`**, on the plan: reporting changes nothing a
close writes. -/
theorem autoCloseR_plan (now : Day) (bm : BlockMin) (p : WfPlan) :
    (autoCloseR now bm p).map Prod.fst = autoClose now p :=
  foldlM_closeStepR_plan now bm autoCloseOrder p Report.empty

/-! ## Every line the close acts on is named once, in fold order -/

theorem filterMap_ids {α : Type} (f : Id → Option α) (idOf : α → Id) :
    ∀ l : List Id, (∀ i ∈ l, ∃ x, f i = some x ∧ idOf x = i) → (l.filterMap f).map idOf = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons i rest ih =>
    intro h
    obtain ⟨x, hx, hid⟩ := h i (List.mem_cons_self ..)
    rw [List.filterMap_cons, hx]
    simp only [List.map_cons, hid]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]

/-- **Completeness, and no invention.**  The report's ids are exactly the ids
the close folds over, in the order it folds — no candidate is missing and no
line the close leaves alone is named. -/
theorem closeReport_ids (g : Grain) (now : Day) (bm : BlockMin) (p : PlanCore) :
    (closeReport g now bm p).map CloseEntry.id = closeCands g now p := by
  unfold closeReport
  apply filterMap_ids
  intro i hi
  have hf := (List.mem_filter.1 (mem_closeCands_iff.1 hi)).2
  revert hf
  cases hg : p.store.get i with
  | none => simp
  | some e =>
    intro hf
    simp only [Option.bind_some]
    unfold closeEntry
    cases hact : closeAct g now p e.val.skel with
    | stay => simp only [hact] at hf; exact absurd hf (by simp)
    | carry => exact ⟨_, rfl, rfl⟩
    | file r => exact ⟨_, rfl, rfl⟩
    | overdue => exact ⟨_, rfl, rfl⟩

theorem mem_closeReport {g : Grain} {now : Day} {bm : BlockMin} {p : PlanCore} {x : CloseEntry}
    (hx : x ∈ closeReport g now bm p) :
    ∃ i e, p.store.get i = some e ∧ closeEntry g now bm p i e.val.skel = some x := by
  unfold closeReport at hx
  obtain ⟨i, _, hix⟩ := List.mem_filterMap.1 hx
  cases hg : p.store.get i with
  | none => rw [hg] at hix; simp at hix
  | some e =>
    rw [hg] at hix
    simp only [Option.bind_some] at hix
    exact ⟨i, e, hg, hix⟩

/-! ## Under a successful close, each entry is what happened -/

/-- A step's stamps, where it does not merge: the row's stamp for the closed
region, appended. -/
theorem skelAfter_stamps_of_not_merging (g : Grain) (r : Region) (k : DocIx) (s : Skel)
    (hm : CloseDid.ofStep (closePolicy g).disposition s.archLine.isSome ≠ .copyMerging) :
    (skelAfter g r k s).stamps = s.stamps ++ (closeStamp g r.ix).toList := by
  have hset : ∀ st : Stamp,
      (Field.viewDemoted (Field.setDemoted (s.stamps ++ [st]) s.line)).getD [] = s.stamps ++ [st] := by
    intro st
    rw [Field.view_set_demoted _ _ (by simp)]
    rfl
  match g with
  | ⟨0, _⟩ => exact hset _
  | ⟨1, _⟩ =>
    cases ha : s.archLine with
    | none =>
      show (Field.viewDemoted (refiledLine _ s.archLine s.line)).getD [] = _
      rw [ha]
      exact hset _
    | some tl => rw [ha] at hm; exact absurd rfl hm
  | ⟨2, _⟩ => simp [skelAfter, closePolicy, closeStamp, stampRuleOf, Skel.stamps]

/-- A step's stamps, where it merges (README gap 53): fork-point `merge_stamps` of
the standing record's history, the line's, and the row's stamp. -/
theorem skelAfter_stamps_merging (g : Grain) (r : Region) (k : DocIx) (s : Skel)
    (hm : CloseDid.ofStep (closePolicy g).disposition s.archLine.isSome = .copyMerging) :
    ∃ tl st, s.archLine = some tl ∧ closeStamp g r.ix = some st ∧
      (skelAfter g r k s).stamps = mergeStamps (stampsOfLine tl) s.stamps st := by
  match g with
  | ⟨0, _⟩ => simp [closePolicy, CloseDid.ofStep, CloseDid.ofDisposition] at hm
  | ⟨2, _⟩ => simp [closePolicy, CloseDid.ofStep, CloseDid.ofDisposition] at hm
  | ⟨1, _⟩ =>
    cases ha : s.archLine with
    | none => rw [ha] at hm; simp [closePolicy, CloseDid.ofStep, CloseDid.ofDisposition] at hm
    | some tl =>
      refine ⟨tl, _, rfl, rfl, ?_⟩
      show (Field.viewDemoted (refiledLine _ s.archLine s.line)).getD [] = _
      rw [ha]
      show (Field.viewDemoted (Field.setDemoted _ _)).getD [] = _
      rw [Field.view_set_demoted _ _
        (List.ne_nil_of_mem (((mergeStamps_spec _ _ _).2 _).2 (Or.inr (Or.inr rfl))))]
      rfl

/-- **Under a successful close, a taken line's step found its target** — the
branches of `stepSkel` in which the close would have refused are not the ones
it took. -/
theorem close_found_the_target {g : Grain} {now : Day} {p q : WfPlan}
    (h : close g now p = .ok q) {i : Id} {e f : Entity}
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) :
    (closeAct g now p.val e.val.skel = .carry →
      ∃ k, carryTarget now p.val = some k ∧ stepSkel g now p.val e.val.skel = { e.val.skel with doc := k }) ∧
    (∀ r, closeAct g now p.val e.val.skel = .file r →
      ∃ k, closeTarget g now p.val = some k ∧
        stepSkel g now p.val e.val.skel = skelAfter g r k e.val.skel) ∧
    (closeAct g now p.val e.val.skel = .overdue →
      ∃ k, overdueTarget p.val = some k ∧ stepSkel g now p.val e.val.skel = { e.val.skel with doc := k }) := by
  obtain ⟨hfr, hall⟩ := close_spec h
  have hsk := close_skel h hp hq
  have hst := (hall i).2 f hq
  rw [closeAct_frame hfr, hsk] at hst
  refine ⟨fun hact => ?_, fun r hact => ?_, fun hact => ?_⟩
  · cases hk : carryTarget now p.val with
    | none =>
      have hstep : stepSkel g now p.val e.val.skel = e.val.skel := by
        unfold stepSkel; simp only [hact, hk]
      rw [hstep, hact] at hst
      exact absurd hst (by simp)
    | some k => exact ⟨k, rfl, by unfold stepSkel; simp only [hact, hk]⟩
  · cases hk : closeTarget g now p.val with
    | none =>
      have hstep : stepSkel g now p.val e.val.skel = e.val.skel := by
        unfold stepSkel; simp only [hact, hk]
      rw [hstep, hact] at hst
      exact absurd hst (by simp)
    | some k => exact ⟨k, rfl, by unfold stepSkel; simp only [hact, hk]⟩
  · cases hk : overdueTarget p.val with
    | none =>
      have hstep : stepSkel g now p.val e.val.skel = e.val.skel := by
        unfold stepSkel; simp only [hact, hk]
      rw [hstep, hact] at hst
      exact absurd hst (by simp)
    | some k => exact ⟨k, rfl, by unfold stepSkel; simp only [hact, hk]⟩

/-- **The report agrees with the close.**  For every entry of a successful
close's report: it names the close's grain; the item is in the plan before and
after; the entry's `src` is the file its live line was in and its `dst` the
file it is in now; the stamps it carries now are the ones it carried with the
entry's `stamp` appended — or, for a `copyMerging` entry (README gap 53), fork-point
`merge_stamps` of its standing record's history, its own and the entry's stamp;
and the entry's minutes are its estimate now.  (Restates
`closeReport_agrees_with_close`, whose stamp clause — `f.stamps = e.stamps ++
x.stamp.toList` for every entry — a merge falsifies:
`closeReport_agrees_with_close_is_refuted_by_a_merge`, Boundary.lean.  It kept its
name at gap 53 over this narrower clause until the stage-4 hardening repair.) -/
theorem closeReport_agrees_with_close_stamping_or_merging {g : Grain} {now : Day} {bm : BlockMin} {p q : WfPlan}
    (h : close g now p = .ok q) {x : CloseEntry} (hx : x ∈ closeReport g now bm p.val) :
    x.grain = g ∧ ∃ e f, p.val.store.get x.id = some e ∧ q.val.store.get x.id = some f ∧
      e.val.live.doc = x.src ∧ f.val.live.doc = x.dst ∧
      (x.did ≠ .copyMerging → f.val.stamps = e.val.stamps ++ x.stamp.toList) ∧
      (x.did = .copyMerging → ∃ t st, e.val.archive = some t ∧ x.stamp = some st ∧
        f.val.stamps = mergeStamps (stampsOfLine t.line) e.val.stamps st) ∧
      x.minutes = estMinutes bm f.val.line := by
  obtain ⟨i, e, hp, hx⟩ := mem_closeReport hx
  -- the id is still in the plan: a close relocates, it never removes
  obtain ⟨hfr, hall⟩ := close_spec h
  have hm := (hall i).1
  rw [hp] at hm
  cases hq : q.val.store.get i with
  | none => rw [hq] at hm; simp at hm
  | some f =>
    have hsk := close_skel h hp hq
    have ht := close_found_the_target h hp hq
    unfold closeEntry at hx
    cases hact : closeAct g now p.val e.val.skel with
    | stay => rw [hact] at hx; simp at hx
    | carry =>
      rw [hact] at hx
      injection hx with hx
      subst hx
      obtain ⟨k, _, hstep⟩ := ht.1 hact
      have hf : f.val.skel = { e.val.skel with doc := k } := hsk.trans hstep
      refine ⟨rfl, e, f, hp, hq, rfl, ?_, fun _ => ?_, fun hc => absurd hc (by simp), ?_⟩
      · show f.val.live.doc = (stepSkel g now p.val e.val.skel).doc
        rw [← hsk]; rfl
      · rw [← Core.skel_stamps, ← Core.skel_stamps, hf]; simp [Skel.stamps]
      · show estMinutes bm (stepSkel g now p.val e.val.skel).line = estMinutes bm f.val.line
        rw [← hsk]; rfl
    | file r =>
      rw [hact] at hx
      injection hx with hx
      subst hx
      obtain ⟨k, _, hstep⟩ := ht.2.1 r hact
      refine ⟨rfl, e, f, hp, hq, rfl, ?_, fun hm => ?_, fun hm => ?_, ?_⟩
      · show f.val.live.doc = (stepSkel g now p.val e.val.skel).doc
        rw [← hsk]; rfl
      · rw [← Core.skel_stamps, ← Core.skel_stamps, hsk, hstep, skelAfter_stamps_of_not_merging _ _ _ _ hm]
      · obtain ⟨tl, st, ha, hs, hst⟩ := skelAfter_stamps_merging g r k e.val.skel hm
        cases he : e.val.archive with
        | none => simp [Core.skel, he] at ha
        | some t =>
          have htl : t.line = tl := by simpa [Core.skel, he] using ha
          refine ⟨t, st, rfl, hs, ?_⟩
          rw [← Core.skel_stamps, hsk, hstep, hst, htl]
          rfl
      · show estMinutes bm (stepSkel g now p.val e.val.skel).line = estMinutes bm f.val.line
        rw [← hsk]; rfl
    | overdue =>
      rw [hact] at hx
      injection hx with hx
      subst hx
      obtain ⟨k, _, hstep⟩ := ht.2.2 hact
      have hf : f.val.skel = { e.val.skel with doc := k } := hsk.trans hstep
      refine ⟨rfl, e, f, hp, hq, rfl, ?_, fun _ => ?_, fun hc => absurd hc (by simp), ?_⟩
      · show f.val.live.doc = (stepSkel g now p.val e.val.skel).doc
        rw [← hsk]; rfl
      · rw [← Core.skel_stamps, ← Core.skel_stamps, hf]; simp [Skel.stamps]
      · show estMinutes bm (stepSkel g now p.val e.val.skel).line = estMinutes bm f.val.line
        rw [← hsk]; rfl

/-- **D1 and D7, in the report.**  A filed entry's destination is `closeTo g now`,
in a file of the next coarser grain's kind; a carried entry's is the week
containing *now*; an overdue entry's is the backlog, a file with no region.  The
report names the destination the owner decided, not the one the closed line
belonged to.  (Restates `closeReport_names_the_region_of_now`, whose second clause
— every entry that is not a carry lands in `closeTo g now` — a `moveOverdue` entry
falsifies since D7.) -/
theorem closeReport_names_the_destination_of_now {g : Grain} {now : Day} {bm : BlockMin} {p q : WfPlan}
    (h : close g now p = .ok q) {x : CloseEntry} (hx : x ∈ closeReport g now bm p.val) :
    (x.did = .carry → docRegion q.val x.dst = some (regionOf week now)) ∧
      (x.did = .moveOverdue → docKindAt q.val x.dst = .backlog ∧ docRegion q.val x.dst = none) ∧
      (x.did ≠ .carry → x.did ≠ .moveOverdue → docRegion q.val x.dst = some (closeTo g now)) := by
  obtain ⟨i, e, hp, hx⟩ := mem_closeReport hx
  obtain ⟨hfr, hall⟩ := close_spec h
  have hm := (hall i).1
  rw [hp] at hm
  cases hq : q.val.store.get i with
  | none => rw [hq] at hm; simp at hm
  | some f =>
    have hsk := close_skel h hp hq
    have ht := close_found_the_target h hp hq
    unfold closeEntry at hx
    cases hact : closeAct g now p.val e.val.skel with
    | stay => rw [hact] at hx; simp at hx
    | carry =>
      rw [hact] at hx
      injection hx with hx
      subst hx
      obtain ⟨k, hk, hstep⟩ := ht.1 hact
      obtain ⟨_, _, hreg⟩ := findDocIx_spec hk
      refine ⟨fun _ => ?_, fun hc => absurd hc (by simp), fun hc => absurd rfl hc⟩
      show docRegion q.val (stepSkel g now p.val e.val.skel).doc = _
      rw [hstep, hfr.2.2]; exact hreg
    | file r =>
      rw [hact] at hx
      injection hx with hx
      subst hx
      have hd := (close_files_a_taken_line_into_closeTo h hp hq hact).1
      refine ⟨fun hc => ?_, fun hc => ?_, fun _ _ => ?_⟩
      · exact absurd hc (CloseDid.ofStep_ne_carry _ _)
      · exact absurd hc (CloseDid.ofStep_ne_moveOverdue _ _)
      · show docRegion q.val (stepSkel g now p.val e.val.skel).doc = _
        rw [← hsk]; exact hd
    | overdue =>
      rw [hact] at hx
      injection hx with hx
      subst hx
      obtain ⟨k, hk, hstep⟩ := ht.2.2 hact
      obtain ⟨_, hkind, hreg⟩ := overdueTarget_spec hk
      refine ⟨fun hc => absurd hc (by simp), fun _ => ?_, fun _ hc => absurd rfl hc⟩
      show docKindAt q.val (stepSkel g now p.val e.val.skel).doc = _ ∧
        docRegion q.val (stepSkel g now p.val e.val.skel).doc = _
      rw [hstep, hfr.2.2, hfr.2.1]; exact ⟨hkind, hreg⟩

/-- **A stamp in the report names the grain that closed**, so the month review
reading `D` and `W` stamps off the report cannot miscount (the row bridge
`closeStamp_names_the_closed_grain`, carried to the entry). -/
theorem closeReport_stamp_names_its_grain {g : Grain} {now : Day} {bm : BlockMin} {p : PlanCore}
    {x : CloseEntry} (hx : x ∈ closeReport g now bm p) {st : Stamp} (hs : x.stamp = some st) :
    st.grain = x.grain := by
  obtain ⟨i, e, _, hx⟩ := mem_closeReport hx
  unfold closeEntry at hx
  split at hx
  · simp at hx
  · injection hx with hx; subst hx; simp at hs
  · rename_i r _
    injection hx with hx; subst hx
    exact closeStamp_names_the_closed_grain g r.ix st hs
  · injection hx with hx; subst hx; simp at hs

/-! ## `autoClose`'s report names each line at most once

The owner's second measured failure was a double stamp: a tree fourteen days
stale stamped every stale pinned item twice.  `autoClose_appends_at_most_one_stamp_or_merges_each_line`
rules it out on the files; this is the same fact on the report, which the month
review reads — an id appears in one grain's entries or in none. -/

/-- `autoCloseR`, unpacked: the three closes, and the three grains' entries in
order, each against the plan its close was handed. -/
theorem autoCloseR_ok {now : Day} {bm : BlockMin} {p q : WfPlan} {r : Report}
    (h : autoCloseR now bm p = .ok (q, r)) :
    ∃ q1 q2, close day now p = .ok q1 ∧ close week now q1 = .ok q2 ∧ close month now q2 = .ok q ∧
      r.closes = closeReport day now bm p.val ++ closeReport week now bm q1.val ++
        closeReport month now bm q2.val := by
  unfold autoCloseR at h
  simp only [autoCloseOrder, List.foldlM_cons, List.foldlM_nil] at h
  unfold closeStepR at h
  cases h1 : close day now p with
  | error x => rw [h1] at h; exact absurd h (by simp [bind, Except.bind, Except.map])
  | ok q1 =>
    rw [h1] at h
    simp only [Except.map, bind, Except.bind] at h
    cases h2 : close week now q1 with
    | error x => rw [h2] at h; exact absurd h (by simp)
    | ok q2 =>
      rw [h2] at h
      simp only at h
      cases h3 : close month now q2 with
      | error x => rw [h3] at h; exact absurd h (by simp)
      | ok q3 =>
        rw [h3] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨q1, q2, rfl, h2, h3, ?_⟩
        simp [Report.append, Report.empty]

theorem mem_closeCands {g : Grain} {now : Day} {p : PlanCore} {i : Id} (h : i ∈ closeCands g now p) :
    ∃ e, p.store.get i = some e ∧ closeAct g now p e.val.skel ≠ .stay := by
  have hf := (List.mem_filter.1 (mem_closeCands_iff.1 h)).2
  revert hf
  cases hg : p.store.get i with
  | none => simp
  | some e =>
    intro hf
    refine ⟨e, rfl, fun hc => ?_⟩
    simp only [hc] at hf
    exact absurd hf (by simp)

theorem not_mem_closeCands_of_stay {g : Grain} {now : Day} {p : PlanCore} {i : Id}
    (h : ∀ f, p.store.get i = some f → closeAct g now p f.val.skel = .stay) : i ∉ closeCands g now p := by
  intro hm
  obtain ⟨e, he, hne⟩ := mem_closeCands hm
  exact hne (h e he)

/-- **A line a close took is not a line any close at that instant takes next.** -/
theorem close_takes_a_line_out_of_every_close {g g' : Grain} {now : Day} {p q : WfPlan}
    (h : close g now p = .ok q) {i : Id} (hi : i ∈ closeCands g now p.val) :
    ∀ f, q.val.store.get i = some f → closeAct g' now q.val f.val.skel = .stay := by
  intro f hq
  obtain ⟨e, hp, hne⟩ := mem_closeCands hi
  obtain ⟨hfr, hall⟩ := close_spec h
  have hsk := close_skel h hp hq
  have hst := (hall i).2 f hq
  rw [closeAct_frame hfr, hsk] at hst
  rw [closeAct_frame hfr, hsk]
  rcases stepSkel_lands_outside_every_closed_region g g' now p.val e.val.skel with ht | ht
  · rw [ht] at hst; exact absurd hst hne
  · exact closeAct_of_closedRegionOf_none ht

/-- A line no close of grain `g` takes stays that way through a close of any grain. -/
theorem close_keeps_a_line_untaken {g g' : Grain} {now : Day} {p q : WfPlan}
    (h : close g' now p = .ok q) {i : Id}
    (hs : ∀ e, p.val.store.get i = some e → closeAct g now p.val e.val.skel = .stay) :
    ∀ f, q.val.store.get i = some f → closeAct g now q.val f.val.skel = .stay := by
  intro f hq
  obtain ⟨hfr, hall⟩ := close_spec h
  have hm := (hall i).1
  rw [hq] at hm
  cases hpi : p.val.store.get i with
  | none => rw [hpi] at hm; simp at hm
  | some e =>
    rw [hpi] at hm
    simp only [Option.map_some, Option.some.injEq] at hm
    rw [closeAct_frame hfr, hm]
    rcases stepSkel_lands_outside_every_closed_region g' g now p.val e.val.skel with ht | ht
    · rw [ht]; exact hs e hpi
    · exact closeAct_of_closedRegionOf_none ht

/-- **Each id at most once in an `autoClose` report** — however stale the tree,
no line is reported by two grains, so no line is reported stamped twice. -/
theorem autoCloseR_names_each_line_at_most_once {now : Day} {bm : BlockMin} {p q : WfPlan}
    {r : Report} (h : autoCloseR now bm p = .ok (q, r)) : (r.closes.map CloseEntry.id).Nodup := by
  obtain ⟨q1, q2, h1, h2, h3, hr⟩ := autoCloseR_ok h
  rw [hr, List.map_append, List.map_append, closeReport_ids, closeReport_ids, closeReport_ids]
  have n1 := closeCands_nodup day now p.val
  have n2 := closeCands_nodup week now q1.val
  have n3 := closeCands_nodup month now q2.val
  refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨n1, n2, ?_⟩, n3, ?_⟩
  · intro a ha b hb hab
    subst hab
    exact not_mem_closeCands_of_stay (close_takes_a_line_out_of_every_close h1 ha) hb
  · intro a ha b hb hab
    subst hab
    rcases List.mem_append.1 ha with ha | ha
    · exact not_mem_closeCands_of_stay
        (close_keeps_a_line_untaken h2 (close_takes_a_line_out_of_every_close h1 ha)) hb
    · exact not_mem_closeCands_of_stay (close_takes_a_line_out_of_every_close h2 ha) hb

/-! ## Where a step can move a line: between the kinds the table names

Used on the wire to widen L22 (`move_has_no_inverse_command`) to the two close
commands: a close moves a line only out of a file of its own grain's kind, and
only into a file of the next coarser grain's kind or, for a wall, the week. -/

/-- A carry is a wall's: recurring lines stay at every grain (`closePolicy_exemptions`). -/
theorem closeAct_carry_is_a_wall {g : Grain} {now : Day} {p : PlanCore} {s : Skel}
    (h : closeAct g now p s = .carry) : ∃ b, s.wallAhead now = some b := by
  unfold closeAct at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · rw [(closePolicy_exemptions g).1] at h; simp [exemptAct] at h
      · split at h
        · simp at h
        · split at h
          · rename_i ahead hw; exact ⟨ahead, hw⟩
          · simp at h

/-- **An overdue action is D7's, and only D7's**: the week row, over a line past
due with `persist` that is not recurring. -/
theorem closeAct_overdue_iff {g : Grain} {now : Day} {p : PlanCore} {s : Skel} :
    closeAct g now p s = .overdue ↔
      (∃ r, closedRegionOf g now p s.doc = some r) ∧ (closePolicy g).takes s.status = true ∧
        s.recurring = false ∧ g = week ∧ s.overdue now = true := by
  constructor
  · intro h
    unfold closeAct at h
    split at h
    · simp at h
    · rename_i r hr
      split at h
      · simp at h
      · rename_i htk
        split at h
        · rw [(closePolicy_exemptions g).1] at h; simp [exemptAct] at h
        · rename_i hrec
          split at h
          · rename_i hc
            exact ⟨⟨r, hr⟩, by simpa using htk, by simpa using hrec,
              (closePolicy_routes_overdue_only_at_week g).1 hc.1, hc.2⟩
          · split at h
            · rename_i b _; cases b <;> simp [(closePolicy_exemptions g).2, exemptAct] at h
            · simp at h
  · rintro ⟨⟨r, hr⟩, htk, hrec, hg, hov⟩
    unfold closeAct
    rw [hr]
    simp only [htk, hrec, Bool.true_eq_false, Bool.false_eq_true, if_false]
    rw [if_pos ⟨(closePolicy_routes_overdue_only_at_week g).2 hg, hov⟩]

theorem closedRegionOf_of_closeAct {g : Grain} {now : Day} {p : PlanCore} {s : Skel}
    (h : closeAct g now p s ≠ .stay) : ∃ r, closedRegionOf g now p s.doc = some r := by
  cases hc : closedRegionOf g now p s.doc with
  | none => exact absurd (closeAct_of_closedRegionOf_none hc) h
  | some r => exact ⟨r, rfl⟩

/-- **A step moves a line only between the kinds the table names.** -/
theorem stepSkel_doc_kinds (g : Grain) (now : Day) (p : PlanCore) (s : Skel)
    (h : (stepSkel g now p s).doc ≠ s.doc) :
    docKindAt p s.doc = kindOfGrain g ∧
      (docKindAt p (stepSkel g now p s).doc = kindOfGrain (coarsen g) ∨
        ((∃ b, s.wallAhead now = some b) ∧ docKindAt p (stepSkel g now p s).doc = .week) ∨
        (s.overdue now = true ∧ docKindAt p (stepSkel g now p s).doc = .backlog)) := by
  cases hact : closeAct g now p s with
  | stay => rw [stepSkel_of_stay hact] at h; exact absurd rfl h
  | carry =>
    obtain ⟨r, hr⟩ := closedRegionOf_of_closeAct (by rw [hact]; simp)
    refine ⟨(closedRegionOf_spec hr).2.1, Or.inr (Or.inl ⟨closeAct_carry_is_a_wall hact, ?_⟩)⟩
    cases hk : carryTarget now p with
    | none =>
      have hs : stepSkel g now p s = s := by unfold stepSkel; simp only [hact, hk]
      rw [hs] at h; exact absurd rfl h
    | some k =>
      have hs : stepSkel g now p s = { s with doc := k } := by unfold stepSkel; simp only [hact, hk]
      rw [hs]; exact (findDocIx_spec hk).2.1
  | file r =>
    obtain ⟨r', hr⟩ := closedRegionOf_of_closeAct (by rw [hact]; simp)
    refine ⟨(closedRegionOf_spec hr).2.1, Or.inl ?_⟩
    cases hk : closeTarget g now p with
    | none =>
      have hs : stepSkel g now p s = s := by unfold stepSkel; simp only [hact, hk]
      rw [hs] at h; exact absurd rfl h
    | some k =>
      have hs : stepSkel g now p s = skelAfter g r k s := by unfold stepSkel; simp only [hact, hk]
      rw [hs] at h ⊢
      rcases skelAfter_doc g r k s with hd | hd
      · rw [hd]; exact (findDocIx_spec hk).2.1
      · rw [hd] at h; exact absurd rfl h
  | overdue =>
    obtain ⟨r, hr⟩ := closedRegionOf_of_closeAct (by rw [hact]; simp)
    refine ⟨(closedRegionOf_spec hr).2.1, Or.inr (Or.inr ⟨(closeAct_overdue_iff.1 hact).2.2.2.2, ?_⟩)⟩
    cases hk : overdueTarget p with
    | none =>
      have hs : stepSkel g now p s = s := by unfold stepSkel; simp only [hact, hk]
      rw [hs] at h; exact absurd rfl h
    | some k =>
      have hs : stepSkel g now p s = { s with doc := k } := by unfold stepSkel; simp only [hact, hk]
      rw [hs]; exact (overdueTarget_spec hk).2.1

end Tm
