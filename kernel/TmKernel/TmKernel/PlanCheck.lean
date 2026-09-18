import TmKernel.Planner
/-!
# L26's eleven single-run laws, as one checker battery (stage 6, track G)

Design §6 writes this pattern once and says getting it right once is most of the stage.  Each
of §8.3's eleven invariants is **three** things and this module holds the first two:

1. **the checker** — a total, decidable `Bool` over `(PlanReq, DayPlan)`;
2. **the reflection lemma** — `checker r d = true ↔ <the Prop the goal states>`;
3. **the discharge** — one line, in the step that has made the battery pass at `dayPlan r`.

The third is not here, and §6.1's `dayPlan_ok` is only half here.  What that means exactly is
the next section, because it is the one thing a reader of this file has to get right.

## What is proved here, and what is emphatically not

This module was written against step P0's `dayPlan` — a window, a budget and **no segments**
— where every checker below is satisfied and `dayPlan_ok_core` was one line.  **Step P1 fills
the day, and the W-14 land step re-proved the lift over the day P1 produces**; the section
"What P1's body does to the lift" below says what that cost and what it found (README gap
385).  Nothing in the eleven checkers changed.

**No goal leaves `Goals.lean` here, and none did then.**  `Goals.lean`'s own stage-6 banner
says why: when this module was written the six block-side checks were vacuous over `dayPlan`,
because no step before P3 placed a Block of its own, so a discharge taken from them would have
been AGENTS §5.2's theorem that compiles and means nothing.  *(Step **P3** changed that: §8.2
choice 5b's reservation is a Block row the planner places, `dayPlan_ok_core` below discharges
the six about it rather than vacuously, and one goal — E1 — left `Goals.lean` in that step.
The tripwire is now `Planner.the_day_assigns_nothing_after_now_but_the_running_block`.)*
The eleven bridge lemmas below (`*_from_the_battery`) make each discharge one line **the day
its step lands**, and not before.  What the reader should take from this file is that reading:
the battery is a **build-time wall**, not a goal.

`dayPlan_ok_core` is a theorem in a shipped module, so the moment P1 placed a segment its
one-line proof stopped compiling and `check.sh` check 1 failed — exactly as designed, and it
is how the two findings below were found at merge time rather than at P5.  That is AGENTS
§3.1 item 1 — *"can a decidable check on the post-state establish it?"* — and it is strictly
stronger than the same obligation sitting in `Goals.lean`, where a step may simply not look.

## Why the battery is parameterised by an eligibility predicate

Design §6.3 found that **five of the eleven are false as written against the fork** and that
the same restriction repairs four of them: §8.2 step 5 skips a `loc:`-constrained, `atomic` or
`max:`-capped item for reasons no §8.3 invariant is about, so a comparison between two
candidates has to be restricted to the candidates its rule is written about.  §6.3 calls that
predicate `eligibleAt` and design §15 gives its **body to step P5**, because it is step 5's
own filter and the assign fold is its first caller.

So this module takes it as a parameter (`Eligible`) rather than writing it:

* writing a second copy here would be the defect AGENTS §5.3 is named after — P5 needs the
  same predicate to *decide* assignment, and the battery must check against the one the fold
  used, not a lookalike;
* writing a stub that answers `true` would be AGENTS §9.2's *"a check no input can fail"*,
  and it would make four of the eleven checkers silently unrestricted, which is precisely the
  false form §6.3 refutes;
* a parameter puts the dependency **in the type**, where `check.sh` and a reader can both see
  it, instead of in a comment.

Two of §6.3's seven rows need no parameter: `noOverbook` and `energyFilterOk` are restated
around the **Active reservation** alone, and `Planner.RuntimeIn.activeId` already exists for
exactly that (its own doc comment says so).  They are in the eligibility-free half.

## The two halves, and which lift is stateable today

* **`checksCore` — seven checks that need no eligibility**: overbook, oneBlock, energyFilter,
  overWall, overBreak, windDown, wallMoved.  `planOkCore` is their conjunction and
  **`dayPlan_ok_core` is the half of §6.1's lift that does not wait for P5** — stated over the
  same seven checkers, and carrying the two hypotheses P1's body makes necessary.
* **`checksEligible el` — four that do**: rank, hot, impossible, batch.  `planOk el` is the
  whole battery at a given eligibility.  **§6.1's `dayPlan_ok` is NOT stated here**, because
  the honest form of it names `Planner.eligibleAt`, which does not exist: the `∀ el` form is
  the *unrestricted* statement, which is the one design §6.3 refutes, and an `∃ el` form is
  satisfied by the predicate that answers `false`.  It is not stateable yet, it is recorded as
  such in `Goals.lean`'s "not stateable yet" list, and the step that writes `eligibleAt`
  states it.  `planOk_of_no_segments` is the base case, and it is now the only place the `∀ el`
  form is available: P1's day has segments, and over them the `∀ el` form is false (see the
  note where its specialisation to `dayPlan` used to stand).

## Non-vacuity (AGENTS §5.2)

A battery whose checkers cannot fail is a battery that means nothing, and §9.2 lists exactly
that.  Every one of the eleven has a witness below (`*_can_fail`) that exhibits a `DayPlan`
the checker **refuses**, and `planOkCore_can_fail` refuses the battery.  Three of the eleven
read the request's plan, so their witnesses carry a hypothesis about it; each such hypothesis
is satisfiable and `Negative.lean`'s cheats 171-173 assert the refusals from the other side.

## D29 / L24

`plan_tail_drop`'s refutation is **not here**.  What is here is the list arithmetic the
refutation and the restatement will both apply —
`a_kept_reservation_defeats_the_prefix_but_not_the_erasure` — which is the whole mathematical
content of D29 with the planner factored out.

**Since W-15 there IS a refutation, in `TmKernel/PlannerWit.lean`, and it is not choice 5b's**
(README gaps 348, 366).  A `PlanReq` can be built now, so the missing witness is no longer the
blocker; what remains blocked is the *reason* D29 names.  §8.2 choice 5b compares
`plan(budget)` with `plan(budget − Δ)`, and
`PlannerWit.the_budget_does_not_reach_the_assigned_set_until_the_assign_fold_lands` proves the
budget cannot reach `assignedOf` at all until **P5** writes the fold.  What the builder did
expose is a second falsity nobody had recorded: the goal's hypotheses leave `PlanReq.run` free,
and D24's seam put the day's past half inside it, so two requests satisfying every hypothesis
disagree about the whole assigned set —
`PlannerWit.plan_tail_drop_as_stage_6_wrote_it_is_refuted_by_the_run_it_does_not_pin`, with
`erasing_the_active_item_does_not_repair_a_law_whose_run_is_free` beside it.

## D9-21, the recursion rule

Every checker recurses over a list the wire can make large, and each is core's `List.all` /
`List.any` / `List.filter` over `d.segments` (≤ 2 × `Planner.maxCands`), `store.dom` or a
bounded diagnostic list — **no new recursion is written here**.  Four of them are nested, so
they are quadratic in their list: `noBlockOverAWall`, `noBlockOverABreak`,
`noDemandingAfterWindDown` (segments × segments), `monotoneInRank` and `hotBeforeQueue`
(dom × dom), `batchDoesNotReachPast` (segments × batch × dom).  That is a *specification*
cost, not a latency one — nothing on the shipped path evaluates `planOk`; it is the object
`dayPlan_ok` is proved about.  A step that ever does run it says so and measures it.
-/

namespace Tm
namespace PlanCheck

open Planner
open Field (Shape Flag DT)

/-! ## The eleven names

AGENTS §5.7: a refusal carries its name.  These are §8.3's eleven, in design §6.1's order. -/

/-- The name a failing check reports. -/
inductive CheckName
  | overbook | oneBlock | energyFilter | overWall | overBreak | windDown
  | wallMoved | rank | hot | impossible | batch
deriving DecidableEq, Repr

/-- **Design §6.1.**  One decidable check over a produced plan, with the name its refusal
carries. -/
structure Check where
  name : CheckName
  run  : PlanReq → DayPlan → Bool

/-! ## The eligibility parameter (design §6.3) -/

/-- §8.2 step 5's filter: is candidate `i` a candidate *this* segment's rule is written
about?  **The body is step P5's** (design §6.3, §15); the battery takes it as a parameter so
that no second copy is written here and no stub answers `true` for everything. -/
abbrev Eligible := PlanReq → DayPlan → Seg → Id → Bool

/-- "Eligible at some slot of the day" — the form four of §6.3's restatements need. -/
def eligibleSomewhere (el : Eligible) (r : PlanReq) (d : DayPlan) (i : Id) : Bool :=
  d.segments.any (fun s => el r d s.val i)

/-! ## The Active reservation (§8.2 choice 5b)

The running block is reserved before the budget is consulted and carries no slot energy, so
two of §8.3's eleven are restated around it.  `Planner.RuntimeIn.activeId` is the kernel's one
reader of which item that is. -/

/-- Is this segment the running block's? -/
def isActive (r : PlanReq) (s : WfSeg) : Bool :=
  match r.state.activeId with
  | some a => decide (s.val.item = some a)
  | none   => false

/-- The day with §8.2 choice 5b's reservation removed.  `Planner.blockSeconds` is **not**
re-implemented (AGENTS §5.3): this hands it a shorter segment list. -/
def withoutActive (r : PlanReq) (d : DayPlan) : DayPlan :=
  { d with segments := d.segments.filter (fun s => !isActive r s) }

theorem withoutActive_segments (r : PlanReq) (d : DayPlan) :
    (withoutActive r d).segments = d.segments.filter (fun s => !isActive r s) := rfl

/-! ## 1. `overbook` — Σ block minutes ≤ budget × block_min, the reservation excepted

Design §6.3 row 1: false as written, because §8.2 choice 5b "gives the running block its
minutes whatever the budget says". -/

/-- §8.3's overbooking law, restated over the blocks that are **not** the Active
reservation.  **In seconds on both sides** (W-14 repair, gap 392): see
`Planner.blockSeconds`, which says why a floored per-row minute count is a weaker law than the
minutes-since-midnight one it replaced. -/
def noOverbook (r : PlanReq) (d : DayPlan) : Bool :=
  decide (blockSeconds (withoutActive r d) ≤ d.budgetBlocks * d.blockMin * 60)

theorem noOverbook_iff (r : PlanReq) (d : DayPlan) :
    noOverbook r d = true ↔
      blockSeconds (withoutActive r d) ≤ d.budgetBlocks * d.blockMin * 60 := by
  simp [noOverbook]

/-! ## 2. `oneBlock` — no block is longer than one block -/

/-- **In seconds** (W-14 repair, gap 392): `s.val.minutes ≤ d.blockMin` floors, and so admits
a Block of `blockMin` minutes **and 59 seconds**.  `pastRows` clips a replayed row at
`min stop now`, an arbitrary second, so such a row is reachable rather than hypothetical. -/
def oneBlockAtATime (_r : PlanReq) (d : DayPlan) : Bool :=
  d.segments.all
    (fun s => decide (s.val.kind = SegKind.block → s.val.stop - s.val.start ≤ d.blockMin * 60))

theorem oneBlockAtATime_iff (r : PlanReq) (d : DayPlan) :
    oneBlockAtATime r d = true ↔
      ∀ s ∈ d.segments, s.val.kind = SegKind.block →
        s.val.stop - s.val.start ≤ d.blockMin * 60 := by
  simp only [oneBlockAtATime, List.all_eq_true, decide_eq_true_eq]

/-! ## 3. `energyFilter` — every block has `item.ci ≤ slot.energy`

Design §6.3 row 2: survives as written only because the Active block carries no slot energy,
"but only by accident".  The restatement makes the reason a hypothesis. -/

/-- One segment's obligation. -/
def energyOk (r : PlanReq) (s : WfSeg) : Bool :=
  isActive r s ||
    match s.val.kind, s.val.item, s.val.energy with
    | SegKind.block, some i, some lvl => decide ((effectiveCi r.plan.val i).val ≤ lvl.val)
    | _, _, _ => true

def energyFilterOk (r : PlanReq) (d : DayPlan) : Bool :=
  d.segments.all (fun s => energyOk r s)

theorem energyOk_iff (r : PlanReq) (s : WfSeg) :
    energyOk r s = true ↔
      ∀ i lvl, isActive r s = false → s.val.kind = SegKind.block → s.val.item = some i →
        s.val.energy = some lvl → (effectiveCi r.plan.val i).val ≤ lvl.val := by
  unfold energyOk
  cases ha : isActive r s with
  | true => simp
  | false =>
    cases hk : s.val.kind <;> cases hi : s.val.item <;> cases he : s.val.energy <;>
      simp_all

def energyFilterOk_spec (r : PlanReq) (d : DayPlan) : Prop :=
  ∀ s ∈ d.segments, ∀ i lvl, isActive r s = false → s.val.kind = SegKind.block →
    s.val.item = some i → s.val.energy = some lvl → (effectiveCi r.plan.val i).val ≤ lvl.val

theorem energyFilterOk_iff (r : PlanReq) (d : DayPlan) :
    energyFilterOk r d = true ↔ energyFilterOk_spec r d := by
  unfold energyFilterOk energyFilterOk_spec
  rw [List.all_eq_true]
  exact ⟨fun h s hs => (energyOk_iff r s).mp (h s hs), fun h s hs => (energyOk_iff r s).mpr (h s hs)⟩

/-! ## 4. `overWall` and 5. `overBreak` — nothing is placed on top of them -/

def noBlockOverAWall (_r : PlanReq) (d : DayPlan) : Bool :=
  d.segments.all (fun b => d.segments.all (fun w =>
    decide (b.val.kind = SegKind.block → w.val.kind = SegKind.wall →
      b.val.stop ≤ w.val.start ∨ w.val.stop ≤ b.val.start)))

theorem noBlockOverAWall_iff (r : PlanReq) (d : DayPlan) :
    noBlockOverAWall r d = true ↔
      ∀ b ∈ d.segments, ∀ w ∈ d.segments,
        b.val.kind = SegKind.block → w.val.kind = SegKind.wall →
        b.val.stop ≤ w.val.start ∨ w.val.stop ≤ b.val.start := by
  simp only [noBlockOverAWall, List.all_eq_true, decide_eq_true_eq]

def noBlockOverABreak (_r : PlanReq) (d : DayPlan) : Bool :=
  d.segments.all (fun b => d.segments.all (fun k =>
    decide (b.val.kind = SegKind.block → k.val.kind = SegKind.brk →
      b.val.stop ≤ k.val.start ∨ k.val.stop ≤ b.val.start)))

theorem noBlockOverABreak_iff (r : PlanReq) (d : DayPlan) :
    noBlockOverABreak r d = true ↔
      ∀ b ∈ d.segments, ∀ k ∈ d.segments,
        b.val.kind = SegKind.block → k.val.kind = SegKind.brk →
        b.val.stop ≤ k.val.start ∨ k.val.stop ≤ b.val.start := by
  simp only [noBlockOverABreak, List.all_eq_true, decide_eq_true_eq]

/-! ## 6. `windDown` — no `ci ≥ 4` block at or after wind-down -/

def windDownOk (r : PlanReq) (b w : WfSeg) : Bool :=
  match b.val.item with
  | none => true
  | some i =>
      decide (b.val.kind = SegKind.block → w.val.kind = SegKind.windDown →
        w.val.start ≤ b.val.start → (effectiveCi r.plan.val i).val < 4)

def noDemandingAfterWindDown (r : PlanReq) (d : DayPlan) : Bool :=
  d.segments.all (fun b => d.segments.all (fun w => windDownOk r b w))

theorem windDownOk_iff (r : PlanReq) (b w : WfSeg) :
    windDownOk r b w = true ↔
      ∀ i, b.val.item = some i → b.val.kind = SegKind.block →
        w.val.kind = SegKind.windDown → w.val.start ≤ b.val.start →
        (effectiveCi r.plan.val i).val < 4 := by
  unfold windDownOk
  constructor
  · intro h i hi hb hw hle
    simp only [hi, decide_eq_true_eq] at h
    exact h hb hw hle
  · intro h
    cases hi : b.val.item with
    | none => rfl
    | some i =>
        simp only [decide_eq_true_eq]
        intro hb hw hle
        exact h i hi hb hw hle

def noDemandingAfterWindDown_spec (r : PlanReq) (d : DayPlan) : Prop :=
  ∀ b ∈ d.segments, ∀ w ∈ d.segments, ∀ i,
    b.val.item = some i → b.val.kind = SegKind.block → w.val.kind = SegKind.windDown →
    w.val.start ≤ b.val.start → (effectiveCi r.plan.val i).val < 4

theorem noDemandingAfterWindDown_iff (r : PlanReq) (d : DayPlan) :
    noDemandingAfterWindDown r d = true ↔ noDemandingAfterWindDown_spec r d := by
  unfold noDemandingAfterWindDown noDemandingAfterWindDown_spec
  simp only [List.all_eq_true]
  constructor
  · intro h b hb w hw; exact (windDownOk_iff r b w).mp (h b hb w hw)
  · intro h b hb w hw; exact (windDownOk_iff r b w).mpr (h b hb w hw)

/-! ## 7. `wallMoved` — a wall sits where its interval says

On absolute seconds, so the statement pins both ends through `Cal.instantOf` in the request's
own zone (README gap 256). -/

def wallUnmoved (r : PlanReq) (s : WfSeg) : Bool :=
  match s.val.item with
  | none => true
  | some i =>
      match r.plan.val.store.get i with
      | none => true
      | some e =>
          match e.val.shape with
          | Shape.interval a b =>
              decide (s.val.kind = SegKind.wall →
                s.val.start = (Cal.instantOf r.tz a.day a.time).sec ∧
                  s.val.stop = (Cal.instantOf r.tz b.day b.time).sec)
          | _ => true

def wallsUnmoved (r : PlanReq) (d : DayPlan) : Bool :=
  d.segments.all (fun s => wallUnmoved r s)

theorem wallUnmoved_iff (r : PlanReq) (s : WfSeg) :
    wallUnmoved r s = true ↔
      ∀ i e a b, s.val.item = some i → r.plan.val.store.get i = some e →
        e.val.shape = Shape.interval a b → s.val.kind = SegKind.wall →
        s.val.start = (Cal.instantOf r.tz a.day a.time).sec ∧
          s.val.stop = (Cal.instantOf r.tz b.day b.time).sec := by
  unfold wallUnmoved
  constructor
  · intro h i e a b hi hg hs hk
    simp only [hi, hg, hs, decide_eq_true_eq] at h
    exact h hk
  · intro h
    split
    · rfl
    · rename_i i hi
      split
      · rfl
      · rename_i e hg
        split
        · rename_i a b hs
          simp only [decide_eq_true_eq]
          intro hk
          exact h i e a b hi hg hs hk
        · rfl

def wallsUnmoved_spec (r : PlanReq) (d : DayPlan) : Prop :=
  ∀ s ∈ d.segments, ∀ i e a b, s.val.item = some i → r.plan.val.store.get i = some e →
    e.val.shape = Shape.interval a b → s.val.kind = SegKind.wall →
    s.val.start = (Cal.instantOf r.tz a.day a.time).sec ∧
      s.val.stop = (Cal.instantOf r.tz b.day b.time).sec

theorem wallsUnmoved_iff (r : PlanReq) (d : DayPlan) :
    wallsUnmoved r d = true ↔ wallsUnmoved_spec r d := by
  unfold wallsUnmoved wallsUnmoved_spec
  rw [List.all_eq_true]
  exact ⟨fun h s hs => (wallUnmoved_iff r s).mp (h s hs),
         fun h s hs => (wallUnmoved_iff r s).mpr (h s hs)⟩

/-! ## 8. `rank` — monotone in rank, among comparable candidates

Design §6.3 row 4: false as written; the two candidates must additionally be **comparable**,
which is `eligibleSomewhere`. -/

def rankPairOk (el : Eligible) (r : PlanReq) (d : DayPlan) (i j : Id) : Bool :=
  match r.plan.val.store.get i, r.plan.val.store.get j with
  | some e, some f =>
      decide (rootPrio r.plan.val i = rootPrio r.plan.val j →
              effectiveCi r.plan.val i = effectiveCi r.plan.val j →
              e.val.live.doc = f.val.live.doc →
              e.val.live.rank < f.val.live.rank →
              eligibleSomewhere el r d i = true →
              eligibleSomewhere el r d j = true →
              j ∈ assignedOf d → i ∈ assignedOf d)
  | _, _ => true

def monotoneInRank (el : Eligible) (r : PlanReq) (d : DayPlan) : Bool :=
  r.plan.val.store.dom.all (fun i =>
    r.plan.val.store.dom.all (fun j => rankPairOk el r d i j))

theorem rankPairOk_iff (el : Eligible) (r : PlanReq) (d : DayPlan) (i j : Id) :
    rankPairOk el r d i j = true ↔
      ∀ e f, r.plan.val.store.get i = some e → r.plan.val.store.get j = some f →
        rootPrio r.plan.val i = rootPrio r.plan.val j →
        effectiveCi r.plan.val i = effectiveCi r.plan.val j →
        e.val.live.doc = f.val.live.doc →
        e.val.live.rank < f.val.live.rank →
        eligibleSomewhere el r d i = true →
        eligibleSomewhere el r d j = true →
        j ∈ assignedOf d → i ∈ assignedOf d := by
  unfold rankPairOk
  constructor
  · intro h e f hi hj
    simp only [hi, hj, decide_eq_true_eq] at h
    exact h
  · intro h
    cases hi : r.plan.val.store.get i with
    | none => rfl
    | some e =>
        cases hj : r.plan.val.store.get j with
        | none => rfl
        | some f =>
            simp only [decide_eq_true_eq]
            exact h e f hi hj

/-! ## 9. `hot` — a hot item is placed before the queue, when it is eligible

Design §6.3 row 5: false as written; a dep-blocked or `Waiting` hot item is not assigned at
all. -/

def hotPairOk (el : Eligible) (r : PlanReq) (d : DayPlan) (i j : Id) : Bool :=
  match r.plan.val.store.get i, r.plan.val.store.get j with
  | some e, some f =>
      decide (Flag.hot ∈ e.val.flags → Flag.hot ∉ f.val.flags →
              eligibleSomewhere el r d i = true →
              ∀ sj ∈ d.segments, sj.val.item = some j →
              ∃ si ∈ d.segments, si.val.item = some i ∧ si.val.start ≤ sj.val.start)
  | _, _ => true

def hotBeforeQueue (el : Eligible) (r : PlanReq) (d : DayPlan) : Bool :=
  r.plan.val.store.dom.all (fun i =>
    r.plan.val.store.dom.all (fun j => hotPairOk el r d i j))

theorem hotPairOk_iff (el : Eligible) (r : PlanReq) (d : DayPlan) (i j : Id) :
    hotPairOk el r d i j = true ↔
      ∀ e f, r.plan.val.store.get i = some e → r.plan.val.store.get j = some f →
        Flag.hot ∈ e.val.flags → Flag.hot ∉ f.val.flags →
        eligibleSomewhere el r d i = true →
        ∀ sj ∈ d.segments, sj.val.item = some j →
        ∃ si ∈ d.segments, si.val.item = some i ∧ si.val.start ≤ sj.val.start := by
  unfold hotPairOk
  constructor
  · intro h e f hi hj
    simp only [hi, hj, decide_eq_true_eq] at h
    exact h
  · intro h
    cases hi : r.plan.val.store.get i with
    | none => rfl
    | some e =>
        cases hj : r.plan.val.store.get j with
        | none => rfl
        | some f =>
            simp only [decide_eq_true_eq]
            exact h e f hi hj

/-! ## 10. `impossible` — an impossible item is still scheduled

Design §6.3 row 6: §7.3's "still scheduled with everything available" is about capacity, not
eligibility.  The checker reads the plan's **own** account of which items are impossible —
`Diagnostics.impossible`, the id and its exact shortfall — because L26 is "decidable over the
produced `DayPlan`".  **P4 landed the other end of that bridge**: §7.3's EDF numbers are
`Planner.edfNumbers` (this comment named `Goals.edfNumbers`, which was a provisional `def … :=
sorry` and is now deleted), a projection of the grant the pass gives the candidate, with
`edfNumbers_is_the_grants_own_impossibility` tying it to `Grant.impossible`.  What is still
missing is the step that fills `Diagnostics.impossible` from those numbers, which is **P8**'s:
until it does, this checker is about a list nothing writes. -/

def impossibleKept (el : Eligible) (r : PlanReq) (d : DayPlan) : Bool :=
  d.diagnostics.impossible.val.all (fun p =>
    decide (eligibleSomewhere el r d p.1 = true → p.1 ∈ assignedOf d))

theorem impossibleKept_iff (el : Eligible) (r : PlanReq) (d : DayPlan) :
    impossibleKept el r d = true ↔
      ∀ p ∈ d.diagnostics.impossible.val,
        eligibleSomewhere el r d p.1 = true → p.1 ∈ assignedOf d := by
  simp only [impossibleKept, List.all_eq_true, decide_eq_true_eq]

/-! ## 11. `batch` — a batch does not reach past an equal-`ci` candidate of its own group

Design §6.3 row 7: a batch is **split** before the filter wherever its members disagree about
`loc:` or `atomic`, so the skipped candidate must additionally be in the same split group —
which is `el` at that very segment. -/

def batchPairOk (el : Eligible) (r : PlanReq) (d : DayPlan) (s : WfSeg) (ids : BatchIds)
    (i j : Id) : Bool :=
  decide (j ∈ ids.val) ||
    match r.plan.val.store.get i, r.plan.val.store.get j with
    | some e, some f =>
        decide (el r d s.val j = true →
                effectiveCi r.plan.val i = effectiveCi r.plan.val j →
                e.val.live.doc = f.val.live.doc →
                f.val.live.rank < e.val.live.rank →
                j ∈ assignedOf d)
    | _, _ => true

def batchDoesNotReachPast (el : Eligible) (r : PlanReq) (d : DayPlan) : Bool :=
  d.segments.all (fun s =>
    match s.val.kind with
    | SegKind.batch ids =>
        ids.val.all (fun i =>
          r.plan.val.store.dom.all (fun j => batchPairOk el r d s ids i j))
    | _ => true)

theorem batchPairOk_iff (el : Eligible) (r : PlanReq) (d : DayPlan) (s : WfSeg)
    (ids : BatchIds) (i j : Id) :
    batchPairOk el r d s ids i j = true ↔
      ∀ e f, j ∉ ids.val → r.plan.val.store.get i = some e →
        r.plan.val.store.get j = some f →
        el r d s.val j = true →
        effectiveCi r.plan.val i = effectiveCi r.plan.val j →
        e.val.live.doc = f.val.live.doc →
        f.val.live.rank < e.val.live.rank →
        j ∈ assignedOf d := by
  unfold batchPairOk
  constructor
  · intro h e f hn hi hj
    simp only [decide_eq_false_iff_not.mpr hn, Bool.false_or, hi, hj,
      decide_eq_true_eq] at h
    exact h
  · intro h
    by_cases hn : j ∈ ids.val
    · simp [hn]
    · simp only [decide_eq_false_iff_not.mpr hn, Bool.false_or]
      cases hi : r.plan.val.store.get i with
      | none => rfl
      | some e =>
          cases hj : r.plan.val.store.get j with
          | none => rfl
          | some f =>
              simp only [decide_eq_true_eq]
              exact h e f hn hi hj

/-! ## The battery -/

/-- The seven checks that need no eligibility predicate. -/
def checksCore : List Check :=
  [ ⟨.overbook,     noOverbook⟩
  , ⟨.oneBlock,     oneBlockAtATime⟩
  , ⟨.energyFilter, energyFilterOk⟩
  , ⟨.overWall,     noBlockOverAWall⟩
  , ⟨.overBreak,    noBlockOverABreak⟩
  , ⟨.windDown,     noDemandingAfterWindDown⟩
  , ⟨.wallMoved,    wallsUnmoved⟩ ]

/-- The four that compare two candidates and so must be restricted to comparable ones. -/
def checksEligible (el : Eligible) : List Check :=
  [ ⟨.rank,       monotoneInRank el⟩
  , ⟨.hot,        hotBeforeQueue el⟩
  , ⟨.impossible, impossibleKept el⟩
  , ⟨.batch,      batchDoesNotReachPast el⟩ ]

/-- **Design §6.1's `checks`.**  The eleven of §8.3, in one place. -/
def checksOf (el : Eligible) : List Check := checksCore ++ checksEligible el

theorem checksOf_length (el : Eligible) : (checksOf el).length = 11 := rfl

theorem checksCore_length : checksCore.length = 7 := rfl

/-- The eligibility-free conjunction. -/
def planOkCore (r : PlanReq) (d : DayPlan) : Bool := checksCore.all (fun c => c.run r d)

/-- **Design §6.1's `planOk`**, at a given eligibility. -/
def planOk (el : Eligible) (r : PlanReq) (d : DayPlan) : Bool :=
  (checksOf el).all (fun c => c.run r d)

/-- **Design §6.1's `checks_all`**, proved once. -/
theorem checks_all (el : Eligible) (r : PlanReq) (d : DayPlan) (h : planOk el r d = true) :
    ∀ c ∈ checksOf el, c.run r d = true := List.all_eq_true.mp h

theorem checksCore_all (r : PlanReq) (d : DayPlan) (h : planOkCore r d = true) :
    ∀ c ∈ checksCore, c.run r d = true := List.all_eq_true.mp h

theorem planOk_imp_core (el : Eligible) (r : PlanReq) (d : DayPlan) (h : planOk el r d = true) :
    planOkCore r d = true := by
  refine List.all_eq_true.mpr (fun c hc => checks_all el r d h c ?_)
  exact List.mem_append_left _ hc

/-! ## The eleven bridges — §6.1 item 3's "one line", written once

Each is the reflection lemma composed with `checks_all`, so the discharge a P step owes is
`<bridge> r (dayPlan r) (dayPlan_ok_core r) …` and nothing else.  **None of them is applied to
`dayPlan` here** (see the module header). -/

theorem overbook_from_the_battery (r : PlanReq) (d : DayPlan) (h : planOkCore r d = true) :
    blockSeconds (withoutActive r d) ≤ d.budgetBlocks * d.blockMin * 60 :=
  (noOverbook_iff r d).mp (checksCore_all r d h ⟨.overbook, noOverbook⟩ (by simp [checksCore]))

theorem one_block_from_the_battery (r : PlanReq) (d : DayPlan) (h : planOkCore r d = true) :
    ∀ s ∈ d.segments, s.val.kind = SegKind.block →
      s.val.stop - s.val.start ≤ d.blockMin * 60 :=
  (oneBlockAtATime_iff r d).mp
    (checksCore_all r d h ⟨.oneBlock, oneBlockAtATime⟩ (by simp [checksCore]))

theorem energy_filter_from_the_battery (r : PlanReq) (d : DayPlan) (h : planOkCore r d = true) :
    energyFilterOk_spec r d :=
  (energyFilterOk_iff r d).mp
    (checksCore_all r d h ⟨.energyFilter, energyFilterOk⟩ (by simp [checksCore]))

theorem no_block_over_a_wall_from_the_battery (r : PlanReq) (d : DayPlan)
    (h : planOkCore r d = true) :
    ∀ b ∈ d.segments, ∀ w ∈ d.segments,
      b.val.kind = SegKind.block → w.val.kind = SegKind.wall →
      b.val.stop ≤ w.val.start ∨ w.val.stop ≤ b.val.start :=
  (noBlockOverAWall_iff r d).mp
    (checksCore_all r d h ⟨.overWall, noBlockOverAWall⟩ (by simp [checksCore]))

theorem no_block_over_a_break_from_the_battery (r : PlanReq) (d : DayPlan)
    (h : planOkCore r d = true) :
    ∀ b ∈ d.segments, ∀ k ∈ d.segments,
      b.val.kind = SegKind.block → k.val.kind = SegKind.brk →
      b.val.stop ≤ k.val.start ∨ k.val.stop ≤ b.val.start :=
  (noBlockOverABreak_iff r d).mp
    (checksCore_all r d h ⟨.overBreak, noBlockOverABreak⟩ (by simp [checksCore]))

theorem wind_down_from_the_battery (r : PlanReq) (d : DayPlan) (h : planOkCore r d = true) :
    noDemandingAfterWindDown_spec r d :=
  (noDemandingAfterWindDown_iff r d).mp
    (checksCore_all r d h ⟨.windDown, noDemandingAfterWindDown⟩ (by simp [checksCore]))

theorem walls_unmoved_from_the_battery (r : PlanReq) (d : DayPlan) (h : planOkCore r d = true) :
    wallsUnmoved_spec r d :=
  (wallsUnmoved_iff r d).mp
    (checksCore_all r d h ⟨.wallMoved, wallsUnmoved⟩ (by simp [checksCore]))

theorem monotone_in_rank_from_the_battery (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : planOk el r d = true) (i j : Id) (hi : i ∈ r.plan.val.store.dom)
    (hj : j ∈ r.plan.val.store.dom) : rankPairOk el r d i j = true := by
  have := checks_all el r d h ⟨.rank, monotoneInRank el⟩ (by simp [checksOf, checksEligible])
  exact List.all_eq_true.mp (List.all_eq_true.mp this i hi) j hj

theorem hot_before_queue_from_the_battery (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : planOk el r d = true) (i j : Id) (hi : i ∈ r.plan.val.store.dom)
    (hj : j ∈ r.plan.val.store.dom) : hotPairOk el r d i j = true := by
  have := checks_all el r d h ⟨.hot, hotBeforeQueue el⟩ (by simp [checksOf, checksEligible])
  exact List.all_eq_true.mp (List.all_eq_true.mp this i hi) j hj

theorem impossible_kept_from_the_battery (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : planOk el r d = true) :
    ∀ p ∈ d.diagnostics.impossible.val,
      eligibleSomewhere el r d p.1 = true → p.1 ∈ assignedOf d :=
  (impossibleKept_iff el r d).mp
    (checks_all el r d h ⟨.impossible, impossibleKept el⟩ (by simp [checksOf, checksEligible]))

/-- `store.get i = some e` puts `i` in the domain — `Store.domSpec`, so the bridges above can
be applied from the goals' own hypothesis shape. -/
theorem mem_dom_of_get (p : PlanCore) (i : Id) (e : Entity) (h : p.store.get i = some e) :
    i ∈ p.store.dom := (p.store.domSpec i).mpr (by rw [h]; rfl)

/-! ## The base case, and the half of §6.1's lift that is stateable today -/

/-- A day with no segments assigns nothing. -/
theorem assignedOf_of_no_segments (d : DayPlan) (h : d.segments = []) : assignedOf d = [] := by
  unfold assignedOf; rw [h]; rfl

/-- Nothing is eligible anywhere on a day with no segments — which is why the whole battery,
eligibility-restricted checks included, holds of one. -/
theorem eligibleSomewhere_of_no_segments (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : d.segments = []) (i : Id) : eligibleSomewhere el r d i = false := by
  unfold eligibleSomewhere; rw [h]; rfl

/-- **The induction's base case.**  Every one of the seven eligibility-free checks holds of a
day with no segments. -/
theorem planOkCore_of_no_segments (r : PlanReq) (d : DayPlan) (h : d.segments = []) :
    planOkCore r d = true := by
  have hw : (withoutActive r d).segments = [] := by
    simp only [withoutActive_segments, h, List.filter_nil]
  have hb : blockSeconds (withoutActive r d) = 0 := by
    simp only [blockSeconds, hw, List.filter_nil, List.foldl_nil]
  simp [planOkCore, checksCore, noOverbook, oneBlockAtATime, energyFilterOk, noBlockOverAWall,
    noBlockOverABreak, noDemandingAfterWindDown, wallsUnmoved, h, hb]

/-- **The base case, whole.**  A day with no segments passes the battery at **every**
eligibility, because nothing is eligible at a slot that does not exist.  This is the only
reason the `∀ el` form holds, and the name of the theorem below says so. -/
theorem planOk_of_no_segments (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : d.segments = []) : planOk el r d = true := by
  have hcore := planOkCore_of_no_segments r d h
  have hel : ∀ i, eligibleSomewhere el r d i = false :=
    eligibleSomewhere_of_no_segments el r d h
  have hrank : monotoneInRank el r d = true := by
    refine List.all_eq_true.mpr (fun i _ => List.all_eq_true.mpr (fun j _ => ?_))
    refine (rankPairOk_iff el r d i j).mpr ?_
    intro e f _ _ _ _ _ _ hie
    simp [hel i] at hie
  have hhot : hotBeforeQueue el r d = true := by
    refine List.all_eq_true.mpr (fun i _ => List.all_eq_true.mpr (fun j _ => ?_))
    refine (hotPairOk_iff el r d i j).mpr ?_
    intro e f _ _ _ _ hie
    simp [hel i] at hie
  have himp : impossibleKept el r d = true :=
    (impossibleKept_iff el r d).mpr (fun p _ hp => by simp [hel p.1] at hp)
  have hbat : batchDoesNotReachPast el r d = true := by
    simp only [batchDoesNotReachPast, h, List.all_nil]
  simp only [planOk, checksOf, List.all_append, checksEligible, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true]
  exact ⟨hcore, hrank, hhot, himp, hbat⟩

/-! ### What P1's body does to the lift, and what the merge had to do about it

Track G proved `dayPlan_ok_core` in one line over step P0's empty day, and said in this
module's header that P1 would delete the theorem the proof rests on and have to re-prove the
lift "carrying the seven invariants".  **It fired, and re-proving it unchanged is not
possible**: `planOkCore r (dayPlan r) = true` is *false* of the day step P1 produces, for two
reasons that are findings and not accidents (README gap 385).

1. **The replayed past is not the planner's placement.**  §8.2 step 1 replays everything that
   ended before `now` from the log (`Planner.pastRows`), Blocks included, and *six* of the
   seven core checks quantify over every Block row of the day.  A Block the log holds can run
   longer than `block_min`, can sit under a wall, can overlap a break and can exhaust the
   budget — none of it the planner's doing, and none of it anything a replan may move.  The
   fork's own proptest draws exactly this line (`planner_invariants.rs:470`:
   `assigned_set(day, w.now)`, "the planner's doing and never count as 'assigned' for §8.3"),
   and `Planner.assignedFrom` already reads it on the item side.
2. **`wallsUnmoved` is the form step P1 refuted.**  It demands that a Wall row's two ends be
   the interval's two ends, which is
   `Planner.plan_never_moves_a_wall_as_stage_6_wrote_it_is_refuted` written as a checker: a
   `buffer:` puts a second Wall row in front of the event and a wall past local midnight is
   clipped to the day.

**No checker was weakened to get past this.**  All eleven are exactly as track G wrote them,
`can_fail` witnesses included.  What the lift gained instead is the two findings **as named
hypotheses** — which is precisely what P1 did to `plan_never_moves_a_wall` itself — so the
statement below is the same conjunction over the same seven checkers and says out loud which
day it is about.  P5 (blocks, `remaining_budget`) and the request decoder (gap 346) are what
discharge them. -/

/-- **Every Block row of the day is replayed from the log or is §8.2 choice 5b's reservation.**
Steps P1, P2 and P3 place walls, the running interruption, the replayed past, the routines, the
evening and the running block; a Wall is not a Block, an interruption is Lost time, and no row
step 2 places is a Block either (`Planner.stepTwoSegs_are_not_blocks`).

**RESTATED AT STEP P3.**  Until P3 this read *"comes from the log, not from the planner"* and
was named `dayPlan_block_rows_come_from_the_log`, over `Planner.a_block_row_is_a_replayed_row`.
Choice 5b's reservation is a Block row the **planner** places — the first one in the stage — so
the old form is false and both names are gone, with `Check.lean` recording the deletion. -/
theorem dayPlan_block_rows_are_replayed_or_reserved (r : PlanReq) (s : WfSeg)
    (hs : s ∈ (dayPlan r).segments) (hk : s.val.kind = SegKind.block) :
    (∃ t ∈ pastRows r, s = segOf t) ∨ (∃ t ∈ reservationSegs r, s = segOf t) :=
  a_block_row_is_replayed_or_reserved r s (dayPlan_segments r ▸ hs) hk

/-- On a day whose log holds no Block, the day's only Block row is the reservation. -/
theorem dayPlan_block_rows_are_the_reservation (r : PlanReq)
    (hnopast : ∀ t ∈ pastRows r, t.kind ≠ SegKind.block) (s : WfSeg)
    (hs : s ∈ (dayPlan r).segments) (hk : s.val.kind = SegKind.block) :
    ∃ t ∈ reservationSegs r, s = segOf t := by
  rcases dayPlan_block_rows_are_replayed_or_reserved r s hs hk with ⟨t, ht, rfl⟩ | h
  · exact absurd ((segOf_kind t).symm.trans hk) (hnopast t ht)
  · exact h

/-- **Every replayed row is a row of the day** — the converse of
`dayPlan_block_rows_are_replayed_or_reserved`, and the half that was missing when the ledger
claimed otherwise (W-14 repair, gap 393). -/
theorem a_replayed_row_is_a_row_of_the_day (r : PlanReq) (t : Seg) (ht : t ∈ pastRows r) :
    segOf t ∈ (dayPlan r).segments := by
  rw [dayPlan_segments]
  refine mem_sortRows.2 (List.mem_map.2 ⟨t, ?_, rfl⟩)
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ ht)))

/-- **A replayed Block *is* assigned**, so `assignedOf (dayPlan r) = []` is **not** a law of
this `dayPlan` (W-14 repair, gap 393).

The merge's own ledger, and the D29 section below it, asserted the opposite and cited
`Planner.dayPlan_assigns_nothing_yet` — a theorem step P1 **deleted**, because its body made
it false.  This is the statement that survives P1: a Block the log holds for today is work
(`SegKind.isWork`), it is a row of the day, and its items are in `assignedOf`.  The fork
counts it too (`DayPlan::assigned`).  What *is* empty is the set §8.3's laws are about,
`Planner.assignedFrom … now`, and — since step P3 put choice 5b's reservation in it —
`Planner.the_day_assigns_nothing_after_now_but_the_running_block` is the tripwire that says so.

`dayPlan_ok_core`'s `hnopast` hypothesis exists for exactly this reason. -/
theorem a_replayed_block_is_assigned (r : PlanReq) (t : Seg) (ht : t ∈ pastRows r)
    (hk : t.kind = SegKind.block) (i : Id) (hi : i ∈ t.items) :
    i ∈ assignedOf (dayPlan r) :=
  (mem_assignedOf _ i).2
    ⟨segOf t, a_replayed_row_is_a_row_of_the_day r t ht, by rw [segOf_kind, hk]; rfl, hi⟩

/-- **The day has no Block row of its own when nothing is running**: on a day whose log holds no
Block and whose runtime holds no reservation, it has none at all.  This is what
`dayPlan_has_no_block_row` used to say unconditionally; step P3 added the second source. -/
theorem dayPlan_has_no_block_row (r : PlanReq)
    (hnopast : ∀ t ∈ pastRows r, t.kind ≠ SegKind.block) (hnorun : r.activeRun = none)
    (s : WfSeg) (hs : s ∈ (dayPlan r).segments) : s.val.kind ≠ SegKind.block := by
  intro hk
  obtain ⟨t, ht, -⟩ := dayPlan_block_rows_are_the_reservation r hnopast s hs hk
  unfold reservationSegs PlanReq.activeRow at ht
  rw [hnorun] at ht
  exact absurd ht (by simp)

/-- **§6.1's lift, its eligibility-free half, re-proved over the day steps P1, P2 and P3
produce.**

The seven checkers are unchanged and the conjunction is the same one.  What the statement
carries is the findings above, named:

* `hnopast` — the log holds no Block for today, so every Block obligation on the day is about
  the row **the planner placed**.  Since step P3 there is exactly one such row, §8.2 choice
  5b's reservation, and this proof discharges all six block-side checks *about it* rather than
  vacuously.  **P5 is where this hypothesis goes**: it is discharged by restating the six
  block-side checks around what the planner assigns at or after `now`
  (`Planner.assignedFrom`), which is the restriction §8.3 is actually about.
* `hagree` and `hplain` — the request's wall index is its own plan's (`PlanReq.wallsAgree`,
  gap 346, the decoder's to establish) and every dated item it holds is written without a
  `buffer:` and inside the day being planned.  These are exactly the hypotheses P1's own
  `Planner.plan_never_moves_a_wall` carries, and for exactly the same reason.
* **`hactive` and `hday` are step P3's, and both are R10 obligations in the same shape**: the
  running block is one `mkActive?` would have built (it started at or before `now`), and the
  `[day]` is one `mkDayCfg?` would have built (it has a block length).  `oneBlockAtATime` is
  false without either — see `Planner.PlanReq.currentBlockEnd_within_a_block`.
* **`hnowcal` is step P3's too**: the instant being planned is inside the calendar, so
  `Planner.segOf`'s forcing is the identity on the reservation's start.  Without it a request
  whose `now` sits on the horizon produces a zero-length reservation row and the interval
  comparisons stop being about anything.

**Six of the seven checks are now non-vacuous whenever something is running**, which is what
step P3 bought: `noOverbook` runs its `withoutActive` filter on a row that really is the
reservation, `oneBlockAtATime` compares a real Block against `block_min`, `energyFilterOk`
takes the `energy = none` branch choice 5b requires, `noBlockOverAWall` is answered by
`Look.freeIntervals`, `noBlockOverABreak` by the past half's clip at `now`, and
`noDemandingAfterWindDown` by `active_run`'s own limit (README gap **437**, refuted).
`PlannerWit.the_reserved_day_is_the_witness_day_and_the_running_block` and
`PlannerWit.the_battery_passes_at_the_reserved_day` compute all of it at a concrete request.

This is **not** a discharge of any `Goals.lean` entry beyond E1, which leaves the file in this
step over its own restatement (`Planner.plan_reserves_one_block_at_a_time`). -/
theorem dayPlan_ok_core (r : PlanReq)
    (hagree : r.wallsAgree = true)
    (hactive : r.activeAgrees = true)
    (hday : r.dayAgrees = true)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd)
    (hnopast : ∀ t ∈ pastRows r, t.kind ≠ SegKind.block)
    (hplain : ∀ (i : Id) (e : Entity) (a b : Field.DT),
      r.plan.val.store.get i = some e → e.val.shape = Shape.interval a b →
      e.val.buffer = none ∧
        r.dayStart ≤ (Cal.instantOf r.tz a.day a.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec ≤ r.dayEnd ∧
        (Cal.instantOf r.tz a.day a.time).sec < (Cal.instantOf r.tz b.day b.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec < LogStamp.yearEnd) :
    planOkCore r (dayPlan r) = true := by
  -- **Every Block row of this day is the reservation**, with everything the checks ask of it.
  have hblk : ∀ s ∈ (dayPlan r).segments, s.val.kind = SegKind.block →
      ∃ q, r.activeRun = some q ∧ s.val.start = r.now.sec ∧ r.now.sec < s.val.stop ∧
        s.val.stop ≤ q.stop ∧ s.val.stop < LogStamp.yearEnd ∧ s.val.energy = none ∧
        ∃ a, r.state.activeId = some a ∧ s.val.item = some a := by
    intro s hs hk
    obtain ⟨t, ht, rfl⟩ := dayPlan_block_rows_are_the_reservation r hnopast s hs hk
    obtain ⟨q, hq, -, -, -, -, -, -⟩ := r.mem_activeRow t ht
    obtain ⟨e1, e2, e3, e4⟩ := the_reservation_row_is_exact r q hq hnowcal t ht
    obtain ⟨-, hen, -, -, -⟩ := r.activeRow_is_an_energyless_block t ht
    obtain ⟨a, hai, hti⟩ := the_reservation_row_names_the_running_item r t ht
    exact ⟨q, hq, e1, e2, e3, e4, by show t.energy = none; exact hen,
      a, hai, by rw [segOf_item]; exact hti⟩
  have h1 : noOverbook r (dayPlan r) = true := by
    have hnil : (withoutActive r (dayPlan r)).segments.filter
        (fun s => decide (s.val.kind = SegKind.block)) = [] := by
      refine List.filter_eq_nil_iff.2 (fun s hs => ?_)
      rw [withoutActive_segments] at hs
      obtain ⟨hs', hna⟩ := List.mem_filter.1 hs
      simp only [decide_eq_true_eq]
      intro hk
      obtain ⟨q, -, -, -, -, -, -, a, hai, hti⟩ := hblk s hs' hk
      have hact : isActive r s = true := by unfold isActive; rw [hai, hti]; simp
      rw [hact] at hna
      simp at hna
    simp [noOverbook, blockSeconds, hnil]
  have h2 : oneBlockAtATime r (dayPlan r) = true := by
    refine (oneBlockAtATime_iff r _).mpr (fun s hs hk => ?_)
    obtain ⟨q, hq, e1, e2, e3, -, -, -⟩ := hblk s hs hk
    have hone := r.the_reservation_is_at_most_one_block q hactive (r.blockMin_pos hday) hq
    obtain ⟨-, -, -, -, hs0, -⟩ := r.activeRun_spec q hq
    have hbm : (dayPlan r).blockMin = r.blockMin := rfl
    rw [hbm]
    omega
  have h3 : energyFilterOk r (dayPlan r) = true := by
    refine (energyFilterOk_iff r _).mpr (fun s hs i lvl _ hk _ he => ?_)
    obtain ⟨-, -, -, -, -, -, hen, -⟩ := hblk s hs hk
    rw [hen] at he
    exact absurd he (by simp)
  have h4 : noBlockOverAWall r (dayPlan r) = true := by
    refine (noBlockOverAWall_iff r _).mpr (fun b hb w hw hbk hwk => ?_)
    obtain ⟨q, hq, e1, e2, e3, e4, -, -⟩ := hblk b hb hbk
    obtain ⟨v, hv, hvlt, hv1, hv2⟩ :=
      a_wall_row_sits_in_a_blocked_span r w (dayPlan_segments r ▸ hw) hwk
    obtain ⟨-, -, -, -, hs0, hlt, -⟩ := r.activeRun_spec q hq
    have hfree : ∀ u, r.now.sec ≤ u → u < q.stop → ¬ (v.1 ≤ u ∧ u < v.2) := by
      intro u hu1 hu2
      have hq1 : q.start ≤ u := by omega
      exact r.the_reservation_is_free_of_every_wall q hq hv hq1 hu2
    have hdisj : q.stop ≤ v.1 ∨ v.2 ≤ r.now.sec := by
      rcases Nat.lt_or_ge v.1 q.stop with hlt1 | hge1
      · rcases Nat.lt_or_ge r.now.sec v.2 with hlt2 | hge2
        · exact absurd (⟨by omega, by omega⟩ :
            v.1 ≤ max r.now.sec v.1 ∧ max r.now.sec v.1 < v.2)
            (hfree (max r.now.sec v.1) (by omega) (by omega))
        · exact Or.inr hge2
      · exact Or.inl hge1
    simp only [clampSec, LogStamp.yearEnd] at hv1
    simp only [LogStamp.yearEnd] at e4
    rcases hdisj with h | h
    · left; omega
    · right; omega
  have h5 : noBlockOverABreak r (dayPlan r) = true := by
    refine (noBlockOverABreak_iff r _).mpr (fun b hb k hk hbk hkk => ?_)
    obtain ⟨q, hq, e1, e2, e3, e4, -, -⟩ := hblk b hb hbk
    obtain ⟨t, ht, rfl⟩ := a_break_row_is_a_replayed_row r k (dayPlan_segments r ▸ hk) hkk
    obtain ⟨-, hlt2, hstop⟩ := pastRows_end_at_now r t ht
    right
    show max (clampSec t.start) (clampSec t.stop) ≤ b.val.start
    rw [e1]
    simp only [clampSec, LogStamp.yearEnd]
    omega
  have h6 : noDemandingAfterWindDown r (dayPlan r) = true := by
    refine (noDemandingAfterWindDown_iff r _).mpr (fun b hb w hw i _ hbk hwk hle => ?_)
    exfalso
    obtain ⟨q, hq, e1, -, -, -, -, -⟩ := hblk b hb hbk
    obtain ⟨hnw, hws⟩ := a_wind_down_row_of_the_day r w (dayPlan_segments r ▸ hw) hwk
    rw [e1] at hle
    rw [hws] at hle
    have hcs : clampSec r.windDownSec = min r.windDownSec (LogStamp.yearEnd - 1) := rfl
    rw [hcs] at hle
    simp only [LogStamp.yearEnd] at hle hnowcal
    omega
  have h7 : wallsUnmoved r (dayPlan r) = true := by
    refine (wallsUnmoved_iff r _).mpr (fun s hs i e a b hi hget hsh hk => ?_)
    obtain ⟨hnbuf, hin, hout, hfwd, hcal⟩ := hplain i e a b hget hsh
    exact plan_never_moves_a_wall r s i e a b hagree hs hk hi hget hsh hnbuf hin hout hfwd hcal
  simp only [planOkCore, checksCore, List.all_cons, List.all_nil, Bool.and_true,
    h1, h2, h3, h4, h5, h6, h7]

/-! **`dayPlan_ok_at_every_eligibility_while_the_day_is_empty` is gone, and its name is why.**
Track G stated it about a `dayPlan` with no segments; P1's `dayPlan` has segments, so that
statement has no subject left.  It loses nothing: what it asserted is `planOk_of_no_segments`
applied to one day, and that lemma stays above, unchanged and general.  The `∀ el` form is
**false** of P1's body — `hotPairOk` asks a hot item's row to start before every row carrying
the queued one, and a permissive `el` makes that a real obligation over the replayed past —
so it is not restated here either; §6.1's honest `dayPlan_ok` still waits on
`Planner.eligibleAt` (gap 365). -/

/-! ## Non-vacuity (AGENTS §5.2)

*"A check no input can fail"* is on §9.2's disguised-gap list, so every one of the eleven
carries a witness that it **refuses** a day.  Five of them refuse unconditionally; six read the
request's plan and so carry hypotheses, and each hypothesis is satisfiable by an ordinary
plan — an absent id, an item with `ci:5`, an `at:` interval, two ranked siblings, a batch.
The Rust cheats of `Negative.lean` assert the same refusals from the other side.

The witnesses are built with `omega`, not `decide`: `Seg.wf` is two `Nat` comparisons and
`wSeg_wf` discharges them once, so this section adds **no** new `decide` or `rfl` witness to
the budget of AGENTS §5.10a. -/

/-- `List.all` is `false` as soon as one member is. -/
theorem all_eq_false_of_mem {α : Type} {l : List α} {p : α → Bool} {x : α} (hx : x ∈ l)
    (h : p x = false) : l.all p = false := by
  cases hall : l.all p with
  | false => rfl
  | true => rw [List.all_eq_true.mp hall x hx] at h; exact absurd h (by simp)

/-- A witness segment, with nothing on it but what the check under test reads. -/
def wSeg (start stop : Nat) (k : SegKind) (it : Option Id) (en : Option (Fin 6)) : Seg :=
  { start := start, stop := stop, kind := k, energy := en, item := it, inst := none,
    flags := SegFlags.none, planned := none, mult := none, note := none }

theorem wSeg_wf (start stop : Nat) (k : SegKind) (it : Option Id) (en : Option (Fin 6))
    (hle : start ≤ stop) (hh : stop < LogStamp.yearEnd) :
    Seg.wf (wSeg start stop k it en) = true := by
  simp only [LogStamp.yearEnd] at hh
  simp [Seg.wf, wSeg, Cal.Instant.wf, hle, hh]

/-- A witness day. -/
def wDay (segs : List WfSeg) (bm bb : Nat) (imp : Capped (Id × Nat)) : DayPlan :=
  { day := 0, window := (0, 86400), blockMin := bm, budgetBlocks := bb, segments := segs,
    diagnostics := { Diagnostics.empty with impossible := imp },
    priorities := Capped.nil, planHash := PlanHash.zero }

theorem wDay_segments (segs : List WfSeg) (bm bb : Nat) (imp : Capped (Id × Nat)) :
    (wDay segs bm bb imp).segments = segs := rfl

/-- §3.1's `ci` default at an id the plan does not hold: three.  The witnesses below use it so
that an "underpowered block" needs no entity. -/
theorem effectiveCi_of_an_absent_id (p : PlanCore) (i : Id) (h : p.store.get i = none) :
    effectiveCi p i = 3 := by
  simp [effectiveCi, fuel, effectiveCiAux, h]

/-- Every witness segment below ends well inside the calendar; `LogStamp.yearEnd` is a `def`,
so `omega` needs it unfolded once (W-14 repair, gap 391).  Still `omega` and not `decide`, so
AGENTS §5.10a's witness budget is unchanged. -/
theorem horizonOk {stop : Nat} (h : stop ≤ 86400 := by omega) : stop < LogStamp.yearEnd := by
  unfold LogStamp.yearEnd; omega

def aBlockOfAnHour : WfSeg :=
  ⟨wSeg 0 3600 SegKind.block none none, wSeg_wf _ _ _ _ _ (by omega) horizonOk⟩

theorem aBlockOfAnHour_is_not_the_reservation (r : PlanReq) : isActive r aBlockOfAnHour = false := by
  unfold isActive aBlockOfAnHour wSeg
  cases r.state.activeId <;> simp

/-! ### 1. `overbook` — an hour of blocks against a budget of nothing -/

def theOverbookedDay : DayPlan := wDay [aBlockOfAnHour] 60 0 Capped.nil

theorem noOverbook_can_fail (r : PlanReq) : noOverbook r theOverbookedDay = false := by
  have hw : (withoutActive r theOverbookedDay).segments = [aBlockOfAnHour] := by
    simp [withoutActive_segments, theOverbookedDay, wDay, aBlockOfAnHour_is_not_the_reservation r]
  have hb : blockSeconds (withoutActive r theOverbookedDay) = 3600 := by
    simp [blockSeconds, hw, aBlockOfAnHour, wSeg]
  have hbud : theOverbookedDay.budgetBlocks * theOverbookedDay.blockMin * 60 = 0 := rfl
  unfold noOverbook
  rw [hb, hbud]
  simp

/-! ### 2. `oneBlock` — an hour-long block on a thirty-minute day -/

def theOverlongBlockDay : DayPlan := wDay [aBlockOfAnHour] 30 4 Capped.nil

theorem oneBlockAtATime_can_fail (r : PlanReq) :
    oneBlockAtATime r theOverlongBlockDay = false := by
  simp [oneBlockAtATime, theOverlongBlockDay, wDay, aBlockOfAnHour, wSeg]

/-! ### 3. `energyFilter` — a `ci = 3` item in a level-0 slot -/

def anUnderpoweredBlock (i : Id) : WfSeg :=
  ⟨wSeg 0 3600 SegKind.block (some i) (some 0), wSeg_wf _ _ _ _ _ (by omega) horizonOk⟩

def theEnergyBreachDay (i : Id) : DayPlan := wDay [anUnderpoweredBlock i] 60 4 Capped.nil

theorem energyFilterOk_can_fail (r : PlanReq) (i : Id)
    (habs : r.plan.val.store.get i = none) (hact : r.state.activeId ≠ some i) :
    energyFilterOk r (theEnergyBreachDay i) = false := by
  have hna : isActive r (anUnderpoweredBlock i) = false := by
    unfold isActive anUnderpoweredBlock wSeg
    cases ha : r.state.activeId with
    | none => rfl
    | some a =>
        simp only [Option.some.injEq, decide_eq_false_iff_not]
        intro hh
        exact hact (ha.trans (congrArg some hh).symm)
  have he : energyOk r (anUnderpoweredBlock i) = false := by
    unfold energyOk
    rw [hna]
    simp [anUnderpoweredBlock, wSeg, effectiveCi_of_an_absent_id _ i habs]
  simp [energyFilterOk, theEnergyBreachDay, wDay, he]

/-! ### 4 and 5. `overWall`, `overBreak` — a block laid across each -/

def aWallAcross : WfSeg :=
  ⟨wSeg 1800 5400 SegKind.wall none none, wSeg_wf _ _ _ _ _ (by omega) horizonOk⟩

def aBreakAcross : WfSeg :=
  ⟨wSeg 1800 5400 SegKind.brk none none, wSeg_wf _ _ _ _ _ (by omega) horizonOk⟩

def theBlockOverAWallDay : DayPlan := wDay [aBlockOfAnHour, aWallAcross] 60 4 Capped.nil

def theBlockOverABreakDay : DayPlan := wDay [aBlockOfAnHour, aBreakAcross] 60 4 Capped.nil

theorem noBlockOverAWall_can_fail (r : PlanReq) :
    noBlockOverAWall r theBlockOverAWallDay = false := by
  simp [noBlockOverAWall, theBlockOverAWallDay, wDay, aBlockOfAnHour, aWallAcross, wSeg]

theorem noBlockOverABreak_can_fail (r : PlanReq) :
    noBlockOverABreak r theBlockOverABreakDay = false := by
  simp [noBlockOverABreak, theBlockOverABreakDay, wDay, aBlockOfAnHour, aBreakAcross, wSeg]

/-! ### 6. `windDown` — a demanding block after the hard end of the day -/

def aWindDown : WfSeg :=
  ⟨wSeg 0 60 SegKind.windDown none none, wSeg_wf _ _ _ _ _ (by omega) horizonOk⟩

def aLateBlock (i : Id) : WfSeg :=
  ⟨wSeg 3600 7200 SegKind.block (some i) none, wSeg_wf _ _ _ _ _ (by omega) horizonOk⟩

def theLateDemandingDay (i : Id) : DayPlan := wDay [aLateBlock i, aWindDown] 60 4 Capped.nil

theorem noDemandingAfterWindDown_can_fail (r : PlanReq) (i : Id)
    (hci : 4 ≤ (effectiveCi r.plan.val i).val) :
    noDemandingAfterWindDown r (theLateDemandingDay i) = false := by
  have hw : windDownOk r (aLateBlock i) aWindDown = false := by
    cases hb : windDownOk r (aLateBlock i) aWindDown with
    | false => rfl
    | true =>
        have hlt := (windDownOk_iff r (aLateBlock i) aWindDown).mp hb i rfl rfl rfl
          (by simp [aLateBlock, aWindDown, wSeg])
        omega
  refine all_eq_false_of_mem (l := (theLateDemandingDay i).segments) (x := aLateBlock i)
    (by simp [theLateDemandingDay, wDay]) ?_
  exact all_eq_false_of_mem (x := aWindDown) (by simp [theLateDemandingDay, wDay]) hw

/-! ### 7. `wallMoved` — a wall placed where there was room -/

def aMovedWall (i : Id) : WfSeg :=
  ⟨wSeg 0 60 SegKind.wall (some i) none, wSeg_wf _ _ _ _ _ (by omega) horizonOk⟩

def theMovedWallDay (i : Id) : DayPlan := wDay [aMovedWall i] 60 4 Capped.nil

theorem wallsUnmoved_can_fail (r : PlanReq) (i : Id) (e : Entity) (a b : DT)
    (hg : r.plan.val.store.get i = some e) (hs : e.val.shape = Shape.interval a b)
    (hne : (Cal.instantOf r.tz a.day a.time).sec ≠ 0) :
    wallsUnmoved r (theMovedWallDay i) = false := by
  have hu : wallUnmoved r (aMovedWall i) = false := by
    cases hb : wallUnmoved r (aMovedWall i) with
    | false => rfl
    | true =>
        have hx := (wallUnmoved_iff r (aMovedWall i)).mp hb i e a b rfl hg hs rfl
        exact absurd hx.1.symm hne
  simp [wallsUnmoved, theMovedWallDay, wDay, hu]

/-! ### 8, 9, 11. `rank`, `hot`, `batch` — the three that compare two candidates

Each takes the **permissive** eligibility (`fun _ _ _ _ => true`), which is the one design §6.3
refutes for a day that places anything; that is the point of the witness. -/

def aBlockFor (j : Id) : WfSeg :=
  ⟨wSeg 0 3600 SegKind.block (some j) none, wSeg_wf _ _ _ _ _ (by omega) horizonOk⟩

def theOnlyJIsAssignedDay (j : Id) : DayPlan := wDay [aBlockFor j] 60 4 Capped.nil

theorem assignedOf_theOnlyJIsAssignedDay (j : Id) :
    assignedOf (theOnlyJIsAssignedDay j) = [j] := rfl

/-- Everything is eligible under the permissive predicate, on a day with a segment. -/
theorem eligibleSomewhere_permissive (r : PlanReq) (j i : Id) :
    eligibleSomewhere (fun _ _ _ _ => true) r (theOnlyJIsAssignedDay j) i = true := rfl

theorem monotoneInRank_can_fail (r : PlanReq) (i j : Id) (e f : Entity)
    (hi : r.plan.val.store.get i = some e) (hj : r.plan.val.store.get j = some f)
    (hid : i ∈ r.plan.val.store.dom) (hjd : j ∈ r.plan.val.store.dom)
    (hp : rootPrio r.plan.val i = rootPrio r.plan.val j)
    (hc : effectiveCi r.plan.val i = effectiveCi r.plan.val j)
    (hdoc : e.val.live.doc = f.val.live.doc)
    (hlt : e.val.live.rank < f.val.live.rank) (hne : i ≠ j) :
    monotoneInRank (fun _ _ _ _ => true) r (theOnlyJIsAssignedDay j) = false := by
  have hpair : rankPairOk (fun _ _ _ _ => true) r (theOnlyJIsAssignedDay j) i j = false := by
    cases hb : rankPairOk (fun _ _ _ _ => true) r (theOnlyJIsAssignedDay j) i j with
    | false => rfl
    | true =>
        have := (rankPairOk_iff _ r _ i j).mp hb e f hi hj hp hc hdoc hlt
          (eligibleSomewhere_permissive r j i) (eligibleSomewhere_permissive r j j)
          (by rw [assignedOf_theOnlyJIsAssignedDay]; simp)
        rw [assignedOf_theOnlyJIsAssignedDay] at this
        simp at this
        exact absurd this hne
  exact all_eq_false_of_mem hid (all_eq_false_of_mem hjd hpair)

theorem hotBeforeQueue_can_fail (r : PlanReq) (i j : Id) (e f : Entity)
    (hi : r.plan.val.store.get i = some e) (hj : r.plan.val.store.get j = some f)
    (hid : i ∈ r.plan.val.store.dom) (hjd : j ∈ r.plan.val.store.dom)
    (hhot : Flag.hot ∈ e.val.flags) (hnot : Flag.hot ∉ f.val.flags) (hne : i ≠ j) :
    hotBeforeQueue (fun _ _ _ _ => true) r (theOnlyJIsAssignedDay j) = false := by
  have hpair : hotPairOk (fun _ _ _ _ => true) r (theOnlyJIsAssignedDay j) i j = false := by
    cases hb : hotPairOk (fun _ _ _ _ => true) r (theOnlyJIsAssignedDay j) i j with
    | false => rfl
    | true =>
        obtain ⟨si, hsi, hit, _⟩ := (hotPairOk_iff _ r _ i j).mp hb e f hi hj hhot hnot
          (eligibleSomewhere_permissive r j i) (aBlockFor j)
          (by simp [theOnlyJIsAssignedDay, wDay]) (by simp [aBlockFor, wSeg])
        simp only [theOnlyJIsAssignedDay, wDay, List.mem_singleton] at hsi
        subst hsi
        simp only [aBlockFor, wSeg, Option.some.injEq] at hit
        exact absurd hit.symm hne
  exact all_eq_false_of_mem hid (all_eq_false_of_mem hjd hpair)

def aBatchSeg (ids : BatchIds) : WfSeg :=
  ⟨wSeg 0 3600 (SegKind.batch ids) none none, wSeg_wf _ _ _ _ _ (by omega) horizonOk⟩

def theBatchDay (ids : BatchIds) : DayPlan := wDay [aBatchSeg ids] 60 4 Capped.nil

theorem assignedOf_theBatchDay (ids : BatchIds) :
    assignedOf (theBatchDay ids) = ids.val := by
  simp [assignedOf, theBatchDay, wDay, segItems, aBatchSeg, wSeg, Seg.items, SegKind.isWork]

theorem batchDoesNotReachPast_can_fail (r : PlanReq) (ids : BatchIds) (i j : Id) (e f : Entity)
    (hmem : i ∈ ids.val) (hnot : j ∉ ids.val) (hjd : j ∈ r.plan.val.store.dom)
    (hi : r.plan.val.store.get i = some e) (hj : r.plan.val.store.get j = some f)
    (hc : effectiveCi r.plan.val i = effectiveCi r.plan.val j)
    (hdoc : e.val.live.doc = f.val.live.doc)
    (hr : f.val.live.rank < e.val.live.rank) :
    batchDoesNotReachPast (fun _ _ _ _ => true) r (theBatchDay ids) = false := by
  have hpair :
      batchPairOk (fun _ _ _ _ => true) r (theBatchDay ids) (aBatchSeg ids) ids i j = false := by
    cases hb : batchPairOk (fun _ _ _ _ => true) r (theBatchDay ids) (aBatchSeg ids) ids i j with
    | false => rfl
    | true =>
        have := (batchPairOk_iff _ r _ _ ids i j).mp hb e f hnot hi hj rfl hc hdoc hr
        rw [assignedOf_theBatchDay] at this
        exact absurd this hnot
  refine all_eq_false_of_mem (l := (theBatchDay ids).segments) (x := aBatchSeg ids)
    (by simp [theBatchDay, wDay]) ?_
  simp only [aBatchSeg, wSeg]
  exact all_eq_false_of_mem hmem (all_eq_false_of_mem hjd hpair)

/-! ### 10. `impossible` — the item the day cannot fit, dropped instead of shown -/

def theDroppedImpossibleDay (i : Id) : DayPlan :=
  wDay [aBlockOfAnHour] 60 4 ⟨[(i, 30)], by simp [maxCands]⟩

theorem impossibleKept_can_fail (r : PlanReq) (i : Id) :
    impossibleKept (fun _ _ _ _ => true) r (theDroppedImpossibleDay i) = false := by
  simp [impossibleKept, theDroppedImpossibleDay, wDay, eligibleSomewhere, assignedOf,
    segItems, aBlockOfAnHour, wSeg, Seg.items, SegKind.isWork]

/-! ### The battery itself refuses -/

theorem planOkCore_can_fail (r : PlanReq) : planOkCore r theBlockOverAWallDay = false := by
  simp [planOkCore, checksCore, noBlockOverAWall_can_fail r]

theorem planOk_can_fail (el : Eligible) (r : PlanReq) :
    planOk el r theBlockOverAWallDay = false := by
  simp [planOk, checksOf, checksCore, noBlockOverAWall_can_fail r]

/-! ## D29 / L24 — what the refutation will apply, with the planner factored out

**The refutation itself is not here, and this is the real reason** (W-14 repair, gap 393).

What stood here until the repair said that `assignedOf (dayPlan r) = []` for every request,
cited `Planner.dayPlan_assigns_nothing_yet`, and concluded that `plan_tail_drop` as stage 6
wrote it is *true* and has nothing to refute.  **Both halves are wrong.**  P1 deleted the
cited theorem, because its body made it false; and `a_replayed_block_is_assigned` above proves
the contrary: a Block today's log holds is work, is a row of the day, and is in `assignedOf`.
`dayPlan_block_rows_are_replayed_or_reserved` is unconditional and `dayPlan_ok_core`'s
`hnopast` hypothesis exists precisely because today's log **can** hold one.

What was missing until W-15 was a **witness**: `PlanReq` carries a `WfPlan`, a `Seal.Run`, a
`Look.Input` and a `Lookahead`, and there was no decoder and no builder for one (gap 346,
gap 348).  `TmKernel/PlannerWit.lean` is the builder; gap 348 is closed, and a concrete request
whose `dayPlan` holds real rows exists (`PlannerWit.theRequest`).  It is still not a request
whose `dayPlan` **places two candidates and a reservation**, because no step of `dayPlan` does
that yet, and the theorem that says so is
`PlannerWit.the_budget_does_not_reach_the_assigned_set_until_the_assign_fold_lands` — **P5 must
delete it**.  So a restatement shipped without choice 5b's refutation would still be a
weakening (AGENTS §3.1 item 3), `plan_tail_drop` is left exactly as it stands, and the debt is
recorded by name in the README.

What *is* provable today is the arithmetic D29 turns on, and it is the whole of it: §8.2 choice
5b reserves the running block **before** the budget is consulted, so a candidate that ranks
ahead of it can leave the day while the reservation stays — and the shorter assignment is then
not a prefix of the longer one, though it is one again once the reservation is erased from
both sides.  That is D29's restatement and its refutation, side by side, over lists. -/

theorem a_kept_reservation_defeats_the_prefix_but_not_the_erasure (a x : Id) (hne : x ≠ a) :
    (¬ ∃ n : Nat, [a] = ([x, a]).take n) ∧
      (∃ n : Nat, ([a] : List Id).erase a = (([x, a] : List Id).erase a).take n) := by
  constructor
  · rintro ⟨n, hn⟩
    have hl : (([x, a] : List Id).take n).length = 1 := by rw [← hn]; rfl
    simp only [List.length_take, List.length_cons, List.length_nil] at hl
    have hn1 : n = 1 := by omega
    subst hn1
    simp at hn
    exact hne hn.symm
  · refine ⟨0, ?_⟩
    simp [hne]

end PlanCheck
end Tm
