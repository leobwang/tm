import TmKernel.Planner
/-!
# L26's eleven single-run laws, as one checker battery (stage 6, track G)

Design §6 writes this pattern once and says getting it right once is most of the stage.  Each
of §8.3's eleven invariants is **three** things and this module holds the first two:

1. **the checker** — a total, decidable `Bool` over `(PlanReq, DayPlan)`;
2. **the reflection lemma** — `checker r d = true ↔ <the Prop the goal states>`;
3. **the discharge** — one line, in the step that has made the battery pass at `dayPlan r`.

The third is not here, and §6.1's dayPlan_ok is only half here.  What that means exactly is
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
predicate eligibleAt and design §15 gives its **body to step P5**, because it is step 5's
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
  whole battery at a given eligibility.  **§6.1's dayPlan_ok is NOT stated here**, because
  the honest form of it names Planner.eligibleAt, which does not exist: the `∀ el` form is
  the *unrestricted* statement, which is the one design §6.3 refutes, and an `∃ el` form is
  satisfied by the predicate that answers `false`.  It is not stateable yet, it is recorded as
  such in `Goals.lean`'s "not stateable yet" list, and the step that writes eligibleAt
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
dayPlan_ok is proved about.  A step that ever does run it says so and measures it.
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
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ht)))))

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

**What step P3 bought is that each of the seven is *discharged* by the reservation** rather
than by an assumption: `noOverbook` runs its `withoutActive` filter on a row that really is the
reservation, `oneBlockAtATime` compares a real Block against `block_min`, `energyFilterOk`
takes the `energy = none` branch choice 5b requires, `noBlockOverAWall` is answered by
`Look.freeIntervals`, `noBlockOverABreak` by the past half's clip at `now`, and
`noDemandingAfterWindDown` by `active_run`'s own limit (README gap **437**, refuted).

**Being discharged by a real row is not the same as having a subject, and the count of the
second is FOUR, not six** (W-17 repair, README gap 678; this paragraph read *"six of the seven
checks are now non-vacuous whenever something is running"* and nothing computed it).  Measured
over `dayPlan theRunningRequest` by `PlannerWit.the_battery_census_at_the_reserved_day`:
`noOverbook` (`withoutActive` leaves `m2`'s hour, 3 600 s against the budget),
`oneBlockAtATime` (three Block rows), `noBlockOverAWall` (three Blocks beside one Wall) and
`wallsUnmoved` (the Wall row's `^g1` is in that store) have subjects; `energyFilterOk`,
`noBlockOverABreak` and `noDemandingAfterWindDown` are **vacuous** — no row carries a slot
energy, there is no Break row, and no Block starts at or after the wind-down.

*(This paragraph ended "and each waits on **P5** (README gap 650)" until W-18, and one of the
three does not: `noBlockOverABreak` wanted a **log with a `break` in it**, not a step.  It has
a subject at `PlannerWit.theCensusRequest` today, on the whole day and on the `withoutPast`
day both, so at that request `checksCore` is **five of seven** **over the whole day** and not
four.  *(W-22 named the day: the sentence gave one number while naming two days, and over the
`withoutPast` day the same count is **four** — `PlannerWit.the_battery_census_at_the_census_request`
computes both and `PlannerWit.lean` §13's prose has said both since W-18.  Nothing was wrong;
one of the two readings was missing.)*  The other two
wait on nothing a witness can supply — see the vacuity section at the end of this file, which
proves it for every `PlanReq` — and they are P5's.)*
`PlannerWit.the_reserved_day_is_the_witness_day_and_the_running_block` and
`PlannerWit.the_battery_passes_at_the_reserved_day` compute the day and the verdict; neither
computes a population, which is why the census is a third theorem and not a reading of those
two.

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
so it is not restated here either; §6.1's honest dayPlan_ok still waits on
Planner.eligibleAt (gap 365).

*(**W-19 proved that sentence.**  It stood here from W-14 as prose, which is the shape AGENTS
§5.2 warns about from the other side — a claim about the code that no run of the code makes.
`PlannerWit.dayPlan_ok_at_every_eligibility_is_refuted` is the whole-day form and
`PlannerWit.dayPlan_ok_from_now_at_every_eligibility_is_refuted` the restricted one, both
computed at `PlannerWit.theQueuedRequest`, where `hotPairOk` fails for the reason this
paragraph names and `rankPairOk` fails beside it.  README gap 850.)* -/

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


/-! ############################################################################
## §8.3's laws over the rows §8.3 is about — step W-17, track G
############################################################################

**The finding this section is built on is not new; acting on it is.**  `PlanCheck`'s own
header records it as finding 1 (README gap 385): the day's Block rows include the ones
`Planner.pastRows` replays from the log, *"none of it the planner's doing, and none of it
anything a replan may move"*.  Step P3 acted on it once, for E1
(`Planner.plan_reserves_one_block_at_a_time`, refuted and restated over the Block rows that
start at or after `now`).  Two things follow from it that P3 did not take, and both are here.

1. **`plan_places_no_block_over_a_wall` is false for the same reason**, and the witness is
   one record: move the calendar's meeting onto a block the morning's log already holds and
   the day the planner produces has a Block row across a Wall row.
   `PlannerWit.plan_places_no_block_over_a_wall_as_stage_6_wrote_it_is_refuted` computes it.
   The restatement is below, over `Planner.assignedFrom`'s own restriction — the fork's
   `assigned_set(day, w.now)` (`planner_invariants.rs:470`) — and it is **not vacuous**:
   §8.2 choice 5b's reservation is such a row.
2. **`dayPlan_ok_core`'s `hnopast` is not a fact about the planner and need not be a
   hypothesis of the lift.**  It says the log holds no Block for today, which is false of
   every real day after breakfast.  `withoutPast` names the restriction instead of assuming
   it away, and `dayPlan_ok_core_from_now` is the same conjunction over the same seven
   checkers with `hnopast` **gone**.  `dayPlan_ok_core` is kept unchanged beside it — the two
   are incomparable (one drops a hypothesis, the other keeps the whole day) and nothing is
   weakened (D5). -/

/-- The day with the **work** rows that started before `now` removed, and nothing else
touched.  Walls, breaks, the wind-down and the sleep row stay: they are the comparands
§8.3's laws put the planner's Blocks beside, not the subjects of them.

`Planner.SegKind.isWork` is the kernel's one reader of "is this row work" — `Planner.
assignedFrom` uses the same one — so this filter is that predicate plus an instant, and no
second reading of either (AGENTS §5.3).  `withoutActive` above is the pattern: hand the
existing checker a shorter segment list rather than write a second checker. -/
def keepFromNow (r : PlanReq) (s : WfSeg) : Bool :=
  !s.val.kind.isWork || decide (r.now.sec ≤ s.val.start)

def withoutPast (r : PlanReq) (d : DayPlan) : DayPlan :=
  { d with segments := d.segments.filter (keepFromNow r) }

theorem withoutPast_segments (r : PlanReq) (d : DayPlan) :
    (withoutPast r d).segments = d.segments.filter (keepFromNow r) := rfl

/-- A row of `withoutPast` is a row of the day, and a **work** row of it starts at or after
`now`. -/
theorem mem_withoutPast (r : PlanReq) (d : DayPlan) (s : WfSeg)
    (h : s ∈ (withoutPast r d).segments) :
    s ∈ d.segments ∧ (s.val.kind.isWork = true → r.now.sec ≤ s.val.start) := by
  rw [withoutPast_segments] at h
  obtain ⟨hs, hf⟩ := List.mem_filter.1 h
  refine ⟨hs, fun hw => ?_⟩
  unfold keepFromNow at hf
  rw [hw] at hf
  simpa using hf

/-- **A Block row that starts at or after `now` is §8.2 choice 5b's reservation** — the
replayed past cannot reach it, because `Planner.pastRows` ends every row it produces at
`now`.  This is `dayPlan_block_rows_are_the_reservation` with the hypothesis discharged
rather than assumed. -/
theorem a_block_row_from_now_is_the_reservation (r : PlanReq) (s : WfSeg)
    (hs : s ∈ (dayPlan r).segments) (hk : s.val.kind = SegKind.block)
    (hnow : r.now.sec ≤ s.val.start) : ∃ t ∈ reservationSegs r, s = segOf t := by
  rcases dayPlan_block_rows_are_replayed_or_reserved r s hs hk with ⟨t, ht, rfl⟩ | h
  · obtain ⟨-, h2, h3⟩ := pastRows_end_at_now r t ht
    have hlt : (segOf t).val.start < r.now.sec := by
      show clampSec t.start < r.now.sec
      simp only [clampSec, LogStamp.yearEnd]; omega
    omega
  · exact h

/-- **§8.3's "no Block over a Wall", over the rows §8.3 is about.**  The goal
`Goals.plan_places_no_block_over_a_wall` leaves `Goals.lean` for this (AGENTS §3.2's burn-down
protocol), and `PlannerWit.plan_places_no_block_over_a_wall_as_stage_6_wrote_it_is_refuted`
ships in the same commit (AGENTS §3.1 item 3: a restatement without its refutation is a
weakening).

The restriction is `Planner.assignedFrom`'s — Block rows that start at or after `now` — which
is the fork's own `assigned_set(day, w.now)` and the one step P3 used for E1.  `hnowcal` is
the R10 hypothesis `dayPlan_ok_core` already carries: the instant being planned is inside the
calendar, so `Planner.segOf`'s forcing is the identity on the reservation's start.

**Not vacuous**: `PlannerWit.the_reserved_day_assigns_the_running_block` exhibits such a row,
and `PlannerWit.the_battery_passes_at_the_reserved_day` puts it beside the calendar's meeting.
**P5 must re-prove it**: the assign fold puts Blocks of its own into this set, and the proof
below discharges the reservation alone. -/
theorem plan_places_no_block_over_a_wall (r : PlanReq)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd) (b w : WfSeg)
    (hb : b ∈ (dayPlan r).segments) (hw : w ∈ (dayPlan r).segments)
    (hbk : b.val.kind = SegKind.block) (hwk : w.val.kind = SegKind.wall)
    (hnow : r.now.sec ≤ b.val.start) :
    b.val.stop ≤ w.val.start ∨ w.val.stop ≤ b.val.start := by
  obtain ⟨t, ht, rfl⟩ := a_block_row_from_now_is_the_reservation r b hb hbk hnow
  obtain ⟨q, hq, -, -, -, -, -, -⟩ := r.mem_activeRow t ht
  obtain ⟨e1, e2, e3, e4⟩ := the_reservation_row_is_exact r q hq hnowcal t ht
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

/-- **§6.1's lift, with `hnopast` GONE** — the same conjunction over the same seven checkers,
about the rows the planner is responsible for.

`dayPlan_ok_core` above carries `hnopast : ∀ t ∈ pastRows r, t.kind ≠ SegKind.block` — *the
log holds no Block for today*.  That is false of every real day after the first block is
worked, and it is not a fact about the planner at all; it is the hypothesis that lets the six
block-side checks reach a Block the planner never placed.  `withoutPast` names the restriction
§8.3 is actually about instead of assuming it away, and this theorem is the result: **five
hypotheses, all of them R10 or decoder obligations, and none of them about the log's
contents.**

Both lifts are kept.  They are **incomparable** — this one drops a hypothesis and shrinks the
day, `dayPlan_ok_core` keeps the whole day and pays for it with `hnopast` — so keeping both
weakens nothing (D5) and each says something the other does not.

**What is non-vacuous here, measured rather than asserted**
(`PlannerWit.the_battery_census_at_the_reserved_day`, which the W-17 repair step wrote — this
sentence cited it for a run before it existed, README gap 678): with a block running,
`oneBlockAtATime`,
`noBlockOverAWall` and `wallsUnmoved` all have real subjects; `noOverbook` is vacuous *here*
because the only surviving Block **is** the Active reservation and `withoutActive` removes it,
which is design §6.3 row 1 taken literally; and `energyFilterOk`, `noBlockOverABreak` and
`noDemandingAfterWindDown` are vacuous over the produced day for reasons that are facts about
the day and are computed in `PlannerWit`, not claimed here.

**W-18:** `noBlockOverABreak` is vacuous at *that* request and not at every one.  A Break row
survives `withoutPast` (`SegKind.isWork` is false of a Break), so a request whose log holds a
`break` gives this lift's own day a Break row beside the reservation —
`PlannerWit.the_battery_census_at_the_census_request` computes it and
`PlannerWit.the_lift_applies_at_the_census_request` fires the lift there.  The other two are
vacuous at **every** request, and the section at the end of this file proves it.

**P5 must re-prove this.**  The assign fold puts Blocks of its own into `withoutPast`'s
surviving set, and every one of the six block-side discharges below is about the reservation
alone. -/
theorem dayPlan_ok_core_from_now (r : PlanReq)
    (hagree : r.wallsAgree = true)
    (hactive : r.activeAgrees = true)
    (hday : r.dayAgrees = true)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd)
    (hplain : ∀ (i : Id) (e : Entity) (a b : Field.DT),
      r.plan.val.store.get i = some e → e.val.shape = Shape.interval a b →
      e.val.buffer = none ∧
        r.dayStart ≤ (Cal.instantOf r.tz a.day a.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec ≤ r.dayEnd ∧
        (Cal.instantOf r.tz a.day a.time).sec < (Cal.instantOf r.tz b.day b.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec < LogStamp.yearEnd) :
    planOkCore r (withoutPast r (dayPlan r)) = true := by
  have hbm : (withoutPast r (dayPlan r)).blockMin = r.blockMin := rfl
  -- **Every Block row that survives the filter is the reservation** — no hypothesis about
  -- the log, because `pastRows` ends every row it produces at `now`.
  have hblk : ∀ s ∈ (withoutPast r (dayPlan r)).segments, s.val.kind = SegKind.block →
      ∃ q, r.activeRun = some q ∧ s.val.start = r.now.sec ∧ r.now.sec < s.val.stop ∧
        s.val.stop ≤ q.stop ∧ s.val.stop < LogStamp.yearEnd ∧ s.val.energy = none ∧
        ∃ a, r.state.activeId = some a ∧ s.val.item = some a := by
    intro s hs hk
    obtain ⟨hsd, hwk⟩ := mem_withoutPast r (dayPlan r) s hs
    have hnow : r.now.sec ≤ s.val.start := hwk (by rw [hk]; rfl)
    obtain ⟨t, ht, rfl⟩ := a_block_row_from_now_is_the_reservation r s hsd hk hnow
    obtain ⟨q, hq, -, -, -, -, -, -⟩ := r.mem_activeRow t ht
    obtain ⟨e1, e2, e3, e4⟩ := the_reservation_row_is_exact r q hq hnowcal t ht
    obtain ⟨-, hen, -, -, -⟩ := r.activeRow_is_an_energyless_block t ht
    obtain ⟨a, hai, hti⟩ := the_reservation_row_names_the_running_item r t ht
    exact ⟨q, hq, e1, e2, e3, e4, by show t.energy = none; exact hen,
      a, hai, by rw [segOf_item]; exact hti⟩
  have h1 : noOverbook r (withoutPast r (dayPlan r)) = true := by
    have hnil : (withoutActive r (withoutPast r (dayPlan r))).segments.filter
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
  have h2 : oneBlockAtATime r (withoutPast r (dayPlan r)) = true := by
    refine (oneBlockAtATime_iff r _).mpr (fun s hs hk => ?_)
    obtain ⟨q, hq, e1, e2, e3, -, -, -⟩ := hblk s hs hk
    have hone := r.the_reservation_is_at_most_one_block q hactive (r.blockMin_pos hday) hq
    obtain ⟨-, -, -, -, hs0, -⟩ := r.activeRun_spec q hq
    rw [hbm]
    omega
  have h3 : energyFilterOk r (withoutPast r (dayPlan r)) = true := by
    refine (energyFilterOk_iff r _).mpr (fun s hs i lvl _ hk _ he => ?_)
    obtain ⟨-, -, -, -, -, -, hen, -⟩ := hblk s hs hk
    rw [hen] at he
    exact absurd he (by simp)
  have h4 : noBlockOverAWall r (withoutPast r (dayPlan r)) = true := by
    refine (noBlockOverAWall_iff r _).mpr (fun b hb w hw hbk hwk => ?_)
    obtain ⟨hwd, -⟩ := mem_withoutPast r (dayPlan r) w hw
    obtain ⟨q, hq, e1, e2, e3, e4, -, -⟩ := hblk b hb hbk
    obtain ⟨v, hv, hvlt, hv1, hv2⟩ :=
      a_wall_row_sits_in_a_blocked_span r w (dayPlan_segments r ▸ hwd) hwk
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
  have h5 : noBlockOverABreak r (withoutPast r (dayPlan r)) = true := by
    refine (noBlockOverABreak_iff r _).mpr (fun b hb k hk hbk hkk => ?_)
    obtain ⟨hkd, -⟩ := mem_withoutPast r (dayPlan r) k hk
    obtain ⟨q, hq, e1, e2, e3, e4, -, -⟩ := hblk b hb hbk
    obtain ⟨t, ht, rfl⟩ := a_break_row_is_a_replayed_row r k (dayPlan_segments r ▸ hkd) hkk
    obtain ⟨-, hlt2, hstop⟩ := pastRows_end_at_now r t ht
    right
    show max (clampSec t.start) (clampSec t.stop) ≤ b.val.start
    rw [e1]
    simp only [clampSec, LogStamp.yearEnd]
    omega
  have h6 : noDemandingAfterWindDown r (withoutPast r (dayPlan r)) = true := by
    refine (noDemandingAfterWindDown_iff r _).mpr (fun b hb w hw i _ hbk hwk hle => ?_)
    exfalso
    obtain ⟨hwd, -⟩ := mem_withoutPast r (dayPlan r) w hw
    obtain ⟨q, hq, e1, -, -, -, -, -⟩ := hblk b hb hbk
    obtain ⟨hnw, hws⟩ := a_wind_down_row_of_the_day r w (dayPlan_segments r ▸ hwd) hwk
    rw [e1] at hle
    rw [hws] at hle
    have hcs : clampSec r.windDownSec = min r.windDownSec (LogStamp.yearEnd - 1) := rfl
    rw [hcs] at hle
    simp only [LogStamp.yearEnd] at hle hnowcal
    omega
  have h7 : wallsUnmoved r (withoutPast r (dayPlan r)) = true := by
    refine (wallsUnmoved_iff r _).mpr (fun s hs i e a b hi hget hsh hk => ?_)
    obtain ⟨hsd, -⟩ := mem_withoutPast r (dayPlan r) s hs
    obtain ⟨hnbuf, hin, hout, hfwd, hcal⟩ := hplain i e a b hget hsh
    exact plan_never_moves_a_wall r s i e a b hagree hsd hk hi hget hsh hnbuf hin hout hfwd hcal
  simp only [planOkCore, checksCore, List.all_cons, List.all_nil, Bool.and_true,
    h1, h2, h3, h4, h5, h6, h7]

/-! ############################################################################
## The vacuity, PROVED rather than counted — stage 6, run W-18, track G
############################################################################

README gap 650 records four checkers that *"range over nothing on any day the planner can
produce today"*, and two `PlannerWit` census theorems **measure** it at two requests.  A
population computed at a request is evidence about that request; it is not the claim, and the
claim is what a reader takes away.  This section proves the claim: for **every** `PlanReq`,
each of those four checkers returns `true` with an **empty** subject, and the reason in each
case is a structural fact about what `Planner.dayPlan` can put in a day today.

Three of the four are therefore *strengthenings* of `dayPlan_ok_core`'s own conjuncts — `h3`
and `h6` there discharge `energyFilterOk` and `noDemandingAfterWindDown` under `hnopast`, and
the theorems below discharge them under nothing and under `hnowcal` respectively.  That is
not a weakening of anything (D5): the lifts keep their statements, and these say the same
`true` is free.

**The method, and what it cannot see.**  Each fact is proved by the row-source case split
`Planner.mem_dayRows` gives — the replayed past, the running interruption, the walls, step 2's
rows, and §8.2 choice 5b's reservation — so it covers every row `dayRows` can hold and
**nothing else**.  It is blind to:

* any checker whose subject is not a row of the day.  `noOverbook`'s subject is an arithmetic
  comparison, `wallsUnmoved`'s is a store lookup, and `monotoneInRank`/`hotBeforeQueue`'s are
  pairs of ids in `store.dom`; **all three are request questions**, not step questions, and
  `PlannerWit.the_battery_census_at_the_census_request` measures them at one named request rather than
  claiming them here;
* what a later step adds.  Every theorem here is a **build-time wall** in a shipped module,
  in the shape of `Planner.the_day_assigns_nothing_after_now_but_the_running_block`: the
  commit that makes `dayPlan` energise a Block, gather a Batch or fill
  `Diagnostics.impossible` stops it compiling, and **P5 and P8 must delete these four**.

**What it does settle, and it is the answer gap 650 asked for**: no *witness* can give these
four a subject.  Two of gap 650's original four were not of this kind — see
`plan_places_no_block_over_a_break` below and `PlannerWit`'s section 14 (written
`13` on branch `w18-g`, where `## 13.` was already taken; renumbered by W-18's land
step, README gap 772). -/

/-- **No row of the day is a Batch row.**  Steps 1, 2 and 3 place the replayed past, the
running interruption, the walls, the routines, the evening and the reservation; `SegKind.batch`
is gathered by §8.2 step 5's assign fold and by nothing else, and the fold is **P5**. -/
theorem the_day_has_no_batch_row (r : PlanReq) (s : WfSeg) (hs : s ∈ (dayPlan r).segments)
    (ids : BatchIds) : s.val.kind ≠ SegKind.batch ids := by
  intro hk
  obtain ⟨t, ht, rfl⟩ := mem_dayRows (dayPlan_segments r ▸ hs)
  have htk : t.kind = SegKind.batch ids := (segOf_kind t).symm.trans hk
  simp only [stepOneSegs, List.mem_append] at ht
  rcases ht with (((((ht | ht) | ht) | ht) | ht) | ht) | ht
  · unfold pastRows at ht
    split at ht
    · cases ht
    · simp only [List.mem_filterMap] at ht
      obtain ⟨g, -, hg⟩ := ht
      split at hg
      · cases hg
      · have he := Option.some.inj hg
        subst he
        revert htk
        cases g.kind <;> simp [pastKind]
  · rw [(interruptRows_are_open_lost_time r t ht).1] at htk; cases htk
  · simp only [List.mem_flatMap] at ht
    obtain ⟨x, -, hx⟩ := ht
    rw [(wallRows_are_walls_of_the_item (r.isTravelDay x.id) x t hx).1] at htk; cases htk
  · rcases routineRows_kinds r _ t ht with h | h | h <;> rw [h] at htk <;> cases htk
  · rw [reservationSegs_are_blocks r t ht] at htk; cases htk
  · rw [r.optionalRows_kinds t ht] at htk; cases htk
  · rw [r.restRows_kinds t ht] at htk; cases htk

/-- **No Block row of the day carries a slot energy.**  A Block row is replayed or reserved
(`dayPlan_block_rows_are_replayed_or_reserved`); `Planner.pastRows` writes `energy := none` on
every row it makes, and choice 5b's reservation carries none by
`Planner.PlanReq.activeRow_is_an_energyless_block`.  A Block gets a level when the assign fold
puts it in an energised slot, which is **P5**. -/
theorem no_block_row_of_the_day_carries_a_slot_energy (r : PlanReq) (s : WfSeg)
    (hs : s ∈ (dayPlan r).segments) (hk : s.val.kind = SegKind.block) : s.val.energy = none := by
  rcases dayPlan_block_rows_are_replayed_or_reserved r s hs hk with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · show t.energy = none
    unfold pastRows at ht
    split at ht
    · cases ht
    · simp only [List.mem_filterMap] at ht
      obtain ⟨g, -, hg⟩ := ht
      split at hg
      · cases hg
      · have he := Option.some.inj hg
        subst he
        rfl
  · obtain ⟨-, hen, -, -, -⟩ := r.activeRow_is_an_energyless_block t ht
    show t.energy = none
    exact hen

/-- **No Block row of the day starts at or after a WindDown row.**  Two facts meet: a WindDown
row exists only when `now < wind_down` (`Planner.PlanReq.eveningRows`' own guard, carried out
by `Planner.a_wind_down_row_of_the_day`), and every Block row of the day starts at or before
`now` — the replayed ones end at `now`, and the reservation starts exactly there.

So `noDemandingAfterWindDown`'s `w.start ≤ b.start` cannot be satisfied by any day
`Planner.dayPlan` produces, whatever the request.  **P5** is the step that places a Block into
the evening (**P7** for an optional), and it must delete this. -/
theorem no_block_row_of_the_day_reaches_the_wind_down (r : PlanReq)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd) (b w : WfSeg)
    (hb : b ∈ (dayPlan r).segments) (hw : w ∈ (dayPlan r).segments)
    (hbk : b.val.kind = SegKind.block) (hwk : w.val.kind = SegKind.windDown) :
    b.val.start < w.val.start := by
  obtain ⟨hnw, hws⟩ := a_wind_down_row_of_the_day r w (dayPlan_segments r ▸ hw) hwk
  have hbs : b.val.start ≤ r.now.sec := by
    rcases dayPlan_block_rows_are_replayed_or_reserved r b hb hbk with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · obtain ⟨-, h2, h3⟩ := pastRows_end_at_now r t ht
      show clampSec t.start ≤ r.now.sec
      simp only [clampSec, LogStamp.yearEnd]
      omega
    · obtain ⟨q, hq, -, -, -, -, -, -⟩ := r.mem_activeRow t ht
      obtain ⟨e1, -, -, -⟩ := the_reservation_row_is_exact r q hq hnowcal t ht
      omega
  rw [hws]
  have hcs : clampSec r.windDownSec = min r.windDownSec (LogStamp.yearEnd - 1) := rfl
  rw [hcs]
  simp only [LogStamp.yearEnd] at hnowcal ⊢
  omega

/-- **The day names no impossible item.**  `Planner.dayDiagnostics` sets `conflicts` and
`notes` and leaves every other field at `Diagnostics.empty`; the step that fills
`Diagnostics.impossible` from §7.3's grants is **P8** (README gap 367's second half — its
first landed at P4 as `Planner.edfNumbers`). -/
theorem the_day_names_no_impossible_item (r : PlanReq) :
    (dayPlan r).diagnostics.impossible.val = [] := rfl

/-! ### The same four, in the battery's own terms

Each returns `true` on every day the planner produces, and each does so **because its
quantifier is empty**.  That is AGENTS §9.2's *"a check no input can fail"* said out loud with
a proof behind it, and it is the honest reading of four of the eleven conjuncts of §6.1's
lift. -/

/-- `energyFilterOk` cannot fail today, because no Block row carries a level to compare.
**Unconditional** — `dayPlan_ok_core`'s `h3` proves the same `true` under `hnopast`. -/
theorem energyFilterOk_is_true_because_its_subject_is_empty (r : PlanReq) :
    energyFilterOk r (dayPlan r) = true :=
  (energyFilterOk_iff r _).mpr (fun s hs i lvl _ hk _ he => by
    rw [no_block_row_of_the_day_carries_a_slot_energy r s hs hk] at he
    exact absurd he (by simp))

/-- `noDemandingAfterWindDown` cannot fail today, because no Block row reaches the wind-down.
Its one hypothesis is R10's, the same `hnowcal` both lifts carry. -/
theorem noDemandingAfterWindDown_is_true_because_its_subject_is_empty (r : PlanReq)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd) :
    noDemandingAfterWindDown r (dayPlan r) = true :=
  (noDemandingAfterWindDown_iff r _).mpr (fun b hb w hw i _ hbk hwk hle =>
    absurd (no_block_row_of_the_day_reaches_the_wind_down r hnowcal b w hb hw hbk hwk)
      (by omega))

/-- A day with no Batch row passes `batchDoesNotReachPast` at **every** eligibility.  Stated
over an arbitrary `DayPlan` so that the whole day and `withoutPast`'s restriction of it both
get it from one proof, rather than two copies of the same case split (AGENTS §5.3). -/
theorem batchDoesNotReachPast_of_no_batch_row (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : ∀ s ∈ d.segments, ∀ ids, s.val.kind ≠ SegKind.batch ids) :
    batchDoesNotReachPast el r d = true := by
  refine List.all_eq_true.2 (fun s hs => ?_)
  have hn := h s hs
  revert hn
  cases s.val.kind <;> intro hn <;> try rfl
  exact absurd rfl (hn _)

/-- A day whose `Diagnostics.impossible` is empty passes `impossibleKept` at **every**
eligibility, for the same reason and with the same generality. -/
theorem impossibleKept_of_no_impossible (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : d.diagnostics.impossible.val = []) : impossibleKept el r d = true := by
  unfold impossibleKept
  rw [h]
  rfl

/-- `batchDoesNotReachPast` cannot fail today, at **any** eligibility, because there is no
Batch row to range over.  The `∀ el` here is not the unrestricted claim design §6.3 refutes —
it is the statement that the choice of `el` cannot matter to an empty quantifier. -/
theorem batchDoesNotReachPast_is_true_because_its_subject_is_empty (el : Eligible)
    (r : PlanReq) : batchDoesNotReachPast el r (dayPlan r) = true :=
  batchDoesNotReachPast_of_no_batch_row el r _ (fun s hs ids => the_day_has_no_batch_row r s hs ids)

/-- `impossibleKept` cannot fail today, at **any** eligibility, because
`Diagnostics.impossible` is the empty list on every day the planner produces. -/
theorem impossibleKept_is_true_because_its_subject_is_empty (el : Eligible) (r : PlanReq) :
    impossibleKept el r (dayPlan r) = true :=
  impossibleKept_of_no_impossible el r _ (the_day_names_no_impossible_item r)

/-! ### The break law, restated over the rows §8.3 is about

**`plan_places_no_block_over_a_break` is FALSE as `Goals.lean` wrote it**, and for the third
time in this stage it is finding 1 (README gap 385) that makes it so: the day's rows include
the ones `Planner.pastRows` replays, and a log that records a `break` while a block is running
gives the day a Break row *inside* a Block row — neither of them the planner's doing.  Step P3
took that clause for E1, W-17 took it for the wall law, and this is the third and last of the
three block-side comparisons it reaches.

`PlannerWit.plan_places_no_block_over_a_break_as_stage_6_wrote_it_is_refuted` is the
refutation, computed on a day whose log holds a break at 07:30 inside `m1`'s 07:05-08:05
block, and it ships in the same commit (AGENTS §3.1 item 3: a restatement without its
refutation is a weakening).

**The restriction is E1's own** — Block rows that start at or after `now`, the fork's
`assigned_set(day, w.now)` (`planner_invariants.rs:470`) — and `hnowcal` is the R10 hypothesis
both lifts already carry.

**It is not vacuous, and its subject is a request question and not a step question**: §8.2
choice 5b's reservation is such a Block row, a Break row is any `break` the day's log holds,
and `PlannerWit.theCensusRequest` has both.  That is what gap 650 got wrong about this
checker — it gave `noBlockOverABreak`'s emptiness to **P5**, and a log with a break in it ends
it today.  **P5 must still re-prove this**: the assign fold puts Blocks of its own into the
set, and the proof below discharges the reservation alone. -/
theorem plan_places_no_block_over_a_break (r : PlanReq)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd) (b k : WfSeg)
    (hb : b ∈ (dayPlan r).segments) (hk : k ∈ (dayPlan r).segments)
    (hbk : b.val.kind = SegKind.block) (hkk : k.val.kind = SegKind.brk)
    (hnow : r.now.sec ≤ b.val.start) :
    b.val.stop ≤ k.val.start ∨ k.val.stop ≤ b.val.start := by
  obtain ⟨t, ht, rfl⟩ := a_block_row_from_now_is_the_reservation r b hb hbk hnow
  obtain ⟨q, hq, -, -, -, -, -, -⟩ := r.mem_activeRow t ht
  obtain ⟨e1, -, -, -⟩ := the_reservation_row_is_exact r q hq hnowcal t ht
  obtain ⟨u, hu, rfl⟩ := a_break_row_is_a_replayed_row r k (dayPlan_segments r ▸ hk) hkk
  obtain ⟨-, hlt2, hstop⟩ := pastRows_end_at_now r u hu
  right
  show max (clampSec u.start) (clampSec u.stop) ≤ (segOf t).val.start
  rw [e1]
  simp only [clampSec, LogStamp.yearEnd]
  omega

/-! ### How far §6.1's dayPlan_ok has come, stated exactly

Design §6.1's lift is `planOk r (dayPlan r) = true` over all **eleven** checkers.  It is still
not stateable in its honest form: four of the eleven take an eligibility predicate, and
Planner.eligibleAt — which P5 writes, because it is step 5's own filter — does not exist
(README gap 365).  The `∀ el` form is the *unrestricted* claim design §6.3 refutes, and an
`∃ el` form is satisfied by the predicate that answers `false`.

What **is** provable today is the theorem below: **nine of the eleven**, at every eligibility,
over `withoutPast`'s day.  And the honest accounting of those nine is the point of stating it
in one place:

* **seven** are `planOkCore`'s, from `dayPlan_ok_core_from_now`; of those seven, three
  (`energyFilterOk`, `noBlockOverABreak`, `noDemandingAfterWindDown`) were vacuous over the
  restricted day at every request the kernel held before this step, and `noBlockOverABreak`
  is vacuous no longer (`PlannerWit.theCensusRequest`);
* **two** are `checksEligible`'s `impossibleKept` and `batchDoesNotReachPast`, and both hold
  **because their subject is empty at every request** — proved above, not measured.  They
  are in this conjunction because the arithmetic of "how much of §6.1's lift is done" is
  otherwise a matter of counting by hand, which README gap 684 is the record of getting
  wrong;
* **two** are missing, and they are the two comparisons: `monotoneInRank` and
  `hotBeforeQueue`.  Both are real obligations over the replayed past at a permissive `el`
  (see the note above `dayPlan_ok_core`'s own deleted `∀ el` corollary), and both wait on P5.

**W-19 turned that last bullet from "missing" into "false", which is a different inheritance.**
`PlannerWit.the_two_comparisons_are_false_at_the_queued_request` computes both conjuncts as
`false` at the permissive eligibility, on a day `dayPlan` really produces and with no mutation,
while `PlannerWit.the_other_nine_hold_where_the_two_fail` computes the other nine as `true` at
the same request.  So **nine is a ceiling**, not a waypoint: no proof quantified over an
arbitrary `el` can reach ten, and `dayPlan_ok_from_now_given_the_two_comparisons` below is
where the residue is named rather than counted.

So the step after this one inherits: nine of eleven conjuncts proved, two of the nine empty
and owed a subject (P5's batch, P8's impossible list), **two refuted at every eligibility and
owed both Planner.eligibleAt and the fold** (README gap 850), and the fold induction design
§6.2 prices at ≈ 4,500 proof lines **not started** — no line of it is claimed here. -/
theorem dayPlan_ok_from_now_except_the_two_comparisons (el : Eligible) (r : PlanReq)
    (hagree : r.wallsAgree = true)
    (hactive : r.activeAgrees = true)
    (hday : r.dayAgrees = true)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd)
    (hplain : ∀ (i : Id) (e : Entity) (a b : Field.DT),
      r.plan.val.store.get i = some e → e.val.shape = Shape.interval a b →
      e.val.buffer = none ∧
        r.dayStart ≤ (Cal.instantOf r.tz a.day a.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec ≤ r.dayEnd ∧
        (Cal.instantOf r.tz a.day a.time).sec < (Cal.instantOf r.tz b.day b.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec < LogStamp.yearEnd) :
    planOkCore r (withoutPast r (dayPlan r)) = true ∧
      impossibleKept el r (withoutPast r (dayPlan r)) = true ∧
      batchDoesNotReachPast el r (withoutPast r (dayPlan r)) = true :=
  ⟨dayPlan_ok_core_from_now r hagree hactive hday hnowcal hplain,
   impossibleKept_of_no_impossible el r _ (the_day_names_no_impossible_item r),
   batchDoesNotReachPast_of_no_batch_row el r _ (fun s hs ids =>
     the_day_has_no_batch_row r s (mem_withoutPast r _ s hs).1 ids)⟩

/-! ### §6.1's `planOk`, assembled — and why the residue is two named conjuncts (W-19)

The theorem above is a **nine-way conjunction written out by hand**, and the arithmetic that
turns "nine of these eleven" into "the eleven `planOk` computes" is a reader's, not the
compiler's.  README gap 684 is the record of getting exactly that arithmetic wrong.  What
follows hands it to the compiler: given the two conjuncts that are missing, `planOk` itself
answers `true`, over `checksOf`'s own list rather than over a transcription of it.

**It assumes two of the eleven and says so in its name.**  That is not a discharge, and the
reason it is worth stating anyway is the theorem beside it:
`PlannerWit.dayPlan_ok_from_now_at_every_eligibility_is_refuted` proves that the two
hypotheses **cannot be dropped** — at the permissive eligibility both are `false` on a day
`dayPlan` really produces, so no proof over an arbitrary `el` will ever remove them.  Together
the two statements say precisely what §6.1's lift is waiting for: not more proof about the
seven core checks, but Planner.eligibleAt and the assign fold that gives the two comparisons
something honest to range over.

*(Before W-19 this file asserted the second half in prose — *"the `∀ el` form is **false** of
P1's body"*, above `dayPlan_ok_core` — and nothing computed it.)* -/
theorem dayPlan_ok_from_now_given_the_two_comparisons (el : Eligible) (r : PlanReq)
    (hagree : r.wallsAgree = true)
    (hactive : r.activeAgrees = true)
    (hday : r.dayAgrees = true)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd)
    (hplain : ∀ (i : Id) (e : Entity) (a b : Field.DT),
      r.plan.val.store.get i = some e → e.val.shape = Shape.interval a b →
      e.val.buffer = none ∧
        r.dayStart ≤ (Cal.instantOf r.tz a.day a.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec ≤ r.dayEnd ∧
        (Cal.instantOf r.tz a.day a.time).sec < (Cal.instantOf r.tz b.day b.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec < LogStamp.yearEnd)
    (hrank : monotoneInRank el r (withoutPast r (dayPlan r)) = true)
    (hhot : hotBeforeQueue el r (withoutPast r (dayPlan r)) = true) :
    planOk el r (withoutPast r (dayPlan r)) = true := by
  obtain ⟨hcore, himp, hbat⟩ :=
    dayPlan_ok_from_now_except_the_two_comparisons el r hagree hactive hday hnowcal hplain
  simp only [planOk, checksOf, List.all_append, checksEligible, List.all_cons,
    List.all_nil, Bool.and_true, hrank, hhot, himp, hbat]
  exact hcore

/-! ############################################################################
## The quiet day: §6.1's lift at TEN of eleven, over the WHOLE day (W-20, track G)
############################################################################

W-19 left the record at **nine of eleven at every eligibility, over
`withoutPast`'s day**, with the two comparisons refuted.  This section adds the
other axis, and it is a different statement in two ways: it is over the **whole**
day rather than `withoutPast`'s restriction of it, and it reaches **ten**.

**The class it is about is named in its hypotheses and is not a special case of
convenience.**  A *quiet* request is one whose log holds no Block for today
(`hnopast`, which `dayPlan_ok_core` already carries) and whose runtime holds no
reservation (`hnorun`).  On such a day the planner assigns nothing at all —
`dayPlan_assigns_nothing_on_a_quiet_day` — and `monotoneInRank`, the first of
W-19's two refuted comparisons, becomes provable.  It is the **tenth** conjunct
of §6.1's lift, and no proof in this repository had it before.

**What that tenth conjunct is worth, measured rather than implied.**  It is
provable here *because its quantifier is empty*: `rankPairOk`'s conclusion is
`j ∈ assignedOf d → i ∈ assignedOf d`, and `assignedOf` is `[]`.
`PlannerWit.the_tenth_is_vacuous_where_the_eleventh_bites` computes the
population as `[]` at the request where the eleventh has one.  So this is a
**proof-coverage** advance over W-19's nine and **not** a subject-coverage one:
the count of the eleven with something to range over does not move, and a reader
taking "ten of eleven" as "ten checkers biting" is over-counting by the same
argument README gap 650 got wrong about `noBlockOverABreak`.

**Ten is a ceiling on the quiet class too, and the eleventh fails for a cause
that has nothing to do with the assign fold.**
`PlannerWit.hotBeforeQueue_is_false_on_a_quiet_day` computes `hotBeforeQueue` as
`false` at a request with **no log, nothing running and no candidates** — so no
step 5, no choice 5b reservation and no replayed past can be blamed.  The cause
is in the checker's own quantifier: `hotPairOk` ranges `sj` over **every**
segment of the day, and a calendar Wall carrying `^g1` is therefore a queue
position that a hot `^m1` with no row of its own has failed to precede.

**That refines README gap 850's inheritance for P5**, and the refinement is the
point of stating it: gap 850 offered P5 two repairs — an eligibleAt that
refuses a candidate at the reservation row, or the fold.  **Neither reaches
`hotBeforeQueue`.**  The only eligibility that repairs it is one that answers
`false` for an item the plan holds but step 5 never queues, and the only other
repair is in the checker, restricting `sj` to `sj.val.kind.isWork` — which is a
restatement of one of L26's eleven and so is P5's to take with its refutation
beside it (AGENTS §3.1 item 3), not this step's to take quietly.  README gap
960. -/

/-- **A quiet day assigns nothing.**  `assignedOf` filters `SegKind.isWork`, which is `Block`
and `Batch` and nothing else; `dayPlan_has_no_block_row` kills the first on a day with no
replayed Block and no reservation, and `the_day_has_no_batch_row` kills the second on every
day until §8.2 step 5 lands.

This is **not** `PlannerWit.the_quiet_day_assigns_nothing`, which is one `decide` at one
request; this is the ∀-statement that request is an instance of. -/
theorem dayPlan_assigns_nothing_on_a_quiet_day (r : PlanReq)
    (hnopast : ∀ t ∈ pastRows r, t.kind ≠ SegKind.block)
    (hnorun : r.activeRun = none) : assignedOf (dayPlan r) = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro i hi
  obtain ⟨s, hs, hw, -⟩ := (mem_assignedOf _ i).1 hi
  have hnb : ∀ ids, s.val.kind ≠ SegKind.batch ids := the_day_has_no_batch_row r s hs
  have hnbl : s.val.kind ≠ SegKind.block := dayPlan_has_no_block_row r hnopast hnorun s hs
  have hfalse : s.val.kind.isWork = false := by
    cases hk : s.val.kind <;> first
      | exact absurd hk hnbl
      | exact absurd hk (hnb _)
      | rfl
  rw [hfalse] at hw
  exact absurd hw (by simp)

/-- **`monotoneInRank` holds of a day that assigns nothing**, at every eligibility.  Stated
over an arbitrary `DayPlan` so that the quiet day and any later empty-assignment day get it
from one proof (AGENTS §5.3), in the shape `batchDoesNotReachPast_of_no_batch_row` already
uses. -/
theorem monotoneInRank_of_nothing_assigned (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : assignedOf d = []) : monotoneInRank el r d = true := by
  refine List.all_eq_true.2 (fun i _ => List.all_eq_true.2 (fun j _ => ?_))
  refine (rankPairOk_iff el r d i j).2 ?_
  intro e f _ _ _ _ _ _ _ _ hmem
  rw [h] at hmem
  exact absurd hmem (by simp)

/-- **TEN of §6.1's eleven, over the whole day, at every eligibility.**  Seven are
`planOkCore`'s, two hold because their subject is empty at every request, and the tenth is
`monotoneInRank`, which this step adds.

The eleventh is `hotBeforeQueue` and it is **refuted** on this very class —
`PlannerWit.hotBeforeQueue_is_false_on_a_quiet_day` — so this conjunction is not a waypoint
towards eleven by this route.  See the section header. -/
theorem dayPlan_ok_on_a_quiet_day_except_hot (el : Eligible) (r : PlanReq)
    (hagree : r.wallsAgree = true)
    (hactive : r.activeAgrees = true)
    (hday : r.dayAgrees = true)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd)
    (hnopast : ∀ t ∈ pastRows r, t.kind ≠ SegKind.block)
    (hnorun : r.activeRun = none)
    (hplain : ∀ (i : Id) (e : Entity) (a b : Field.DT),
      r.plan.val.store.get i = some e → e.val.shape = Shape.interval a b →
      e.val.buffer = none ∧
        r.dayStart ≤ (Cal.instantOf r.tz a.day a.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec ≤ r.dayEnd ∧
        (Cal.instantOf r.tz a.day a.time).sec < (Cal.instantOf r.tz b.day b.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec < LogStamp.yearEnd) :
    planOkCore r (dayPlan r) = true ∧
      monotoneInRank el r (dayPlan r) = true ∧
      impossibleKept el r (dayPlan r) = true ∧
      batchDoesNotReachPast el r (dayPlan r) = true :=
  ⟨dayPlan_ok_core r hagree hactive hday hnowcal hnopast hplain,
   monotoneInRank_of_nothing_assigned el r _
     (dayPlan_assigns_nothing_on_a_quiet_day r hnopast hnorun),
   impossibleKept_is_true_because_its_subject_is_empty el r,
   batchDoesNotReachPast_is_true_because_its_subject_is_empty el r⟩

/-- **§6.1's `planOk` itself, assembled from the ten plus the one** — so that "ten of eleven"
is the compiler's arithmetic over `checksOf`'s list and not a reader's over a transcription of
it.  README gap 684 is the record of doing that arithmetic by hand and getting it wrong, and
this is the whole-day sibling of `dayPlan_ok_from_now_given_the_two_comparisons`.

**It assumes one of the eleven and its name says so.**  What makes it worth stating is what
stands beside it: `PlannerWit.a_quiet_day_does_not_pass_the_whole_battery` proves the
hypothesis cannot be dropped, and `PlannerWit.the_quiet_battery_passes_at_the_quiet_request`
is the instance in which it holds. -/
theorem dayPlan_ok_on_a_quiet_day_given_hot (el : Eligible) (r : PlanReq)
    (hagree : r.wallsAgree = true)
    (hactive : r.activeAgrees = true)
    (hday : r.dayAgrees = true)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd)
    (hnopast : ∀ t ∈ pastRows r, t.kind ≠ SegKind.block)
    (hnorun : r.activeRun = none)
    (hplain : ∀ (i : Id) (e : Entity) (a b : Field.DT),
      r.plan.val.store.get i = some e → e.val.shape = Shape.interval a b →
      e.val.buffer = none ∧
        r.dayStart ≤ (Cal.instantOf r.tz a.day a.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec ≤ r.dayEnd ∧
        (Cal.instantOf r.tz a.day a.time).sec < (Cal.instantOf r.tz b.day b.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec < LogStamp.yearEnd)
    (hhot : hotBeforeQueue el r (dayPlan r) = true) :
    planOk el r (dayPlan r) = true := by
  obtain ⟨hcore, hrank, himp, hbat⟩ :=
    dayPlan_ok_on_a_quiet_day_except_hot el r hagree hactive hday hnowcal hnopast hnorun hplain
  simp only [planOk, checksOf, List.all_append, checksEligible, List.all_cons,
    List.all_nil, Bool.and_true, hrank, hhot, himp, hbat]
  exact hcore

/-! ############################################################################
## G1's fold: the two clauses README gap 806 left unpinned, and gap 877's consumer
############################################################################

Gap 806 records that three of `pick`'s five clauses are ∀-theorems
(`Planner.PlanReq.assignFold_ok`) and that **`g.live` and the atomic run are pinned by
witnesses only**, because both are statements about the walk's history rather than about the
value it produces.  Gap 806 item 4 names **G1** as the step that clears it.  This is that
step, and the resolution is that the history does not have to be reconstructed: `assignStep`
is universally quantified over the accumulator it is handed, so a ∀-theorem about **one step
at an arbitrary accumulator** is a ∀-theorem about every point of the fold's own walk.

The three theorems below are stated as **gates** — the contrapositive — because that is what
a clause of `pick` *is*: a group the clause refuses does not get the slot.  Stating them the
other way round ("the group that got the slot was live") is the same content and is weaker to
use, because the fold's later steps carry the group forward with its `spent` already moved.

**These live here and not in `Planner.lean` because `Planner.lean`'s step bodies are track P's
this run** (W-20's brief).  They are G1's induction lemmas; the step that writes the fold
induction proper consumes them where they stand.
-/

/-- **`pick`'s first clause, as a ∀-theorem** (README gap 806, half one): a step never hands a
slot to a group that owes nothing.  Whatever the accumulator, whatever the slot, whatever the
budget: if the group at `gi` is not `live`, then the slot was already its own before the step,
which is to say the step did not give it. -/
theorem the_cursor_refuses_a_group_that_owes_nothing (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat)
    (gi : Nat) (g : Group) (hg : a.groups[gi]? = some g) (hdead : g.live = false)
    (hfresh : a.slotOf[x.2]? ≠ some (some gi)) :
    (r.assignStep slots breaks budget a x).slotOf[x.2]? ≠ some (some gi) := by
  intro h
  refine hfresh ?_
  rcases PlanReq.assignStep_cases r slots breaks budget a x with heq | ⟨gj, gg, hgj, hpg, -, heq⟩
  · rwa [heq] at h
  · rw [heq] at h
    simp only at h
    by_cases hlt : x.2 < a.slotOf.length
    · rw [List.getElem?_set_self hlt] at h
      have hji : gj = gi := by simpa using h
      rw [hji] at hgj
      rw [(Option.some.inj (hgj.symm.trans hg) : gg = g)] at hpg
      unfold PlanReq.groupFitsSlot at hpg
      rw [hdead] at hpg
      simp at hpg
    · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hlt)] at h
      exact absurd h (by simp)

/-- **`pick`'s fifth clause, as a ∀-theorem** (README gap 806, half two): a step never hands a
slot to a non-`splittable` group whose remaining run does not fit from that slot on.
`contiguousFits` is read at the accumulator's **own** `slotOf`, which is what makes this a
statement about the assignment as it then stood — the thing gap 806 says a property of the
produced value cannot express. -/
theorem the_cursor_refuses_an_atomic_group_whose_run_is_broken (r : PlanReq)
    (slots : List Look.Slot) (breaks : List (Nat × Nat)) (budget : Nat) (a : Assign)
    (x : (Fin 6 × Look.Slot) × Nat) (gi : Nat) (g : Group) (hg : a.groups[gi]? = some g)
    (hat : g.splittable = false)
    (hbroken : contiguousFits slots a.slotOf breaks x.2 g.leftMin = false)
    (hfresh : a.slotOf[x.2]? ≠ some (some gi)) :
    (r.assignStep slots breaks budget a x).slotOf[x.2]? ≠ some (some gi) := by
  intro h
  refine hfresh ?_
  rcases PlanReq.assignStep_cases r slots breaks budget a x with heq | ⟨gj, gg, hgj, hpg, -, heq⟩
  · rwa [heq] at h
  · rw [heq] at h
    simp only at h
    by_cases hlt : x.2 < a.slotOf.length
    · rw [List.getElem?_set_self hlt] at h
      have hji : gj = gi := by simpa using h
      rw [hji] at hgj
      rw [(Option.some.inj (hgj.symm.trans hg) : gg = g)] at hpg
      unfold PlanReq.groupFitsSlot at hpg
      rw [hat, hbroken] at hpg
      simp at hpg
    · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hlt)] at h
      exact absurd h (by simp)

/-- **The cursor skips no group that fits** — README gap 877's consumer.

`Planner.pickedGroup_is_the_first_that_fits` states two things and
`Planner.PlanReq.assignStep_cases` destructures away the second; gap 877 records that the
"every earlier group fails" half had a computed subject and no proof consuming it.  This is
that proof.  It is the statement §7.4's key order is *for*: a slot that went to `gi` went
there because everything ranked ahead of `gi` was refused at that very slot, which is the
claim the fork's `for (gi, g) in groups.iter().enumerate()` actually makes.

It is also the shape `monotoneInRank`'s honest discharge needs — "the higher-ranked candidate
was not merely unlucky, it failed the filter" — which is why G1 is the step that owes it. -/
theorem the_cursor_skips_no_group_that_fits (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat)
    (gi j : Nat) (gj : Group) (hj : j < gi) (hgj : a.groups[j]? = some gj)
    (hnew : a.slotOf[x.2]? ≠ some (some gi))
    (h : (r.assignStep slots breaks budget a x).slotOf[x.2]? = some (some gi)) :
    r.groupFitsSlot slots a.slotOf breaks x.2 x.1.1 x.1.2 gj = false := by
  unfold PlanReq.assignStep at h
  split at h
  · exact absurd h hnew
  · split at h
    · exact absurd h hnew
    · rename_i gk hp
      split at h
      · exact absurd h hnew
      · rename_i g hgk
        simp only at h
        by_cases hlt : x.2 < a.slotOf.length
        · rw [List.getElem?_set_self hlt] at h
          have hki : gk = gi := by simpa using h
          obtain ⟨-, hbefore⟩ := pickedGroup_is_the_first_that_fits _ a.groups gk hp
          exact hbefore j (by omega) gj hgj
        · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hlt)] at h
          exact absurd h (by simp)

/-! ### The same clause, lifted over the whole walk by induction

The gates above are per-step.  This is the induction, and it is the first one in this
repository that runs over `Planner.PlanReq.assignFold` for something other than
`Planner.PlanReq.AssignOk`.  What it carries is the one consequence of `g.live` that survives
every later step: a group the cursor ever gave a slot to had a **positive commitment**, and
`Planner.PlanReq.assignStep_keeps_the_group` says no step moves `commitMin`. -/

/-- The invariant: every slot that is taken was taken by a group that asks for minutes. -/
def OwesSomething (a : Assign) : Prop :=
  ∀ (i gi : Nat) (g : Group),
    a.slotOf[i]? = some (some gi) → a.groups[gi]? = some g → 0 < g.commitMin

theorem assignStart_owes (r : PlanReq) : OwesSomething r.assignStart := by
  intro i gi g h _
  unfold PlanReq.assignStart at h
  simp only [List.getElem?_replicate] at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem assignStep_owes (r : PlanReq) (slots : List Look.Slot) (breaks : List (Nat × Nat))
    (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat) (h : OwesSomething a) :
    OwesSomething (r.assignStep slots breaks budget a x) := by
  rcases PlanReq.assignStep_cases r slots breaks budget a x with heq | ⟨gj, gg, hgj, hpg, -, heq⟩
  · rw [heq]; exact h
  · rw [heq]
    have hpos : 0 < gg.commitMin := by
      unfold PlanReq.groupFitsSlot at hpg
      simp only [Bool.and_eq_true] at hpg
      have hlive : gg.live = true := hpg.1.1.1.1
      unfold Group.live at hlive
      simp only [decide_eq_true_eq] at hlive
      omega
    intro i gi g hi hgi
    simp only at hi hgi
    by_cases hig : gi = gj
    · subst hig
      rw [List.getElem?_set_self (lt_of_getElem?_some hgj)] at hgi
      rw [← Option.some.inj hgi]
      exact hpos
    · rw [List.getElem?_set_ne (by omega)] at hgi
      by_cases hix : i = x.2
      · subst hix
        by_cases hlt : x.2 < a.slotOf.length
        · rw [List.getElem?_set_self hlt] at hi
          exact absurd (by simpa using hi : gj = gi) (by omega)
        · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hlt)] at hi
          exact absurd hi (by simp)
      · rw [List.getElem?_set_ne (by omega)] at hi
        exact h i gi g hi hgi

theorem foldl_assignStep_owes (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a : Assign), OwesSomething a →
      OwesSomething (l.foldl (r.assignStep slots breaks budget) a)
  | [], _, ha => ha
  | _ :: xs, a, ha => by
      simp only [List.foldl_cons]
      exact foldl_assignStep_owes r slots breaks budget xs _ (assignStep_owes r slots breaks budget a _ ha)

/-- **The cursor gives no slot to a group that owes nothing** — over the whole of §8.2 step
5's walk, for every `PlanReq`.  README gap 806's first half, as a property of the produced
assignment rather than of one step. -/
theorem assignFold_owes (r : PlanReq) : OwesSomething r.assignFold :=
  foldl_assignStep_owes r r.todaySlots r.todayBreaks (remainingBudget r) _ _ (assignStart_owes r)

/-- **The invariant's consumer, with `OwesSomething` nowhere in its statement.**  A predicate
that is only ever mentioned by theorems *about* it is the `Planner.Ranked.gatherable := true`
shape (README gap 875): constant-folding it to `fun _ => True` leaves every such theorem green.
This is the statement that stops being provable when it is —- the fold's own guarantee, written
without the invariant's name.  D40. -/
theorem the_cursor_gives_no_slot_to_a_group_that_owes_nothing (r : PlanReq) (i gi : Nat)
    (g : Group) (hs : r.assignFold.slotOf[i]? = some (some gi))
    (hg : r.assignFold.groups[gi]? = some g) : 0 < g.commitMin :=
  assignFold_owes r i gi g hs hg

/-! ############################################################################
## W-21: the eligibility axis collapses, and ELEVEN of eleven on a quiet day
############################################################################

Two facts §6.1's lift did not have, and they are one fact seen from two sides.

**(a) `planOk` is ANTITONE in the eligibility.**  All four eligibility-dependent checkers read
`el` in the ANTECEDENT of their implication — `rankPairOk`, `hotPairOk` and `impossibleKept`
through `eligibleSomewhere`, `batchPairOk` at the segment directly — so an `el` that admits
FEWER candidates can only make the battery easier.  `planOk_antitone` is that, and
`planOk_at_every_eligibility` is its corollary: the whole `∀ el` axis this file has been
carrying since W-19 **collapses to one computation at the permissive eligibility**.

That is what W-19's "nine is a ceiling" argument was, made into a theorem rather than a
reading: `PlannerWit.the_two_comparisons_are_false_at_the_queued_request` computes both
comparisons `false` at `permissive`, and because `permissive` is the top of this order a
refutation there is a refutation of the `∀ el` form and of nothing weaker.  It is also what
makes **(b)** worth stating, because (b) is a hypothesis ON `el` and antitonicity says which
direction such a hypothesis may point.

**(b) `WorkAnchored`, and eleven of eleven.**  README gap 960 left the eleventh conjunct
`false` on the quiet class and named two repairs, one of them P5's restatement of an L26 goal.
There is a third, and it touches neither the checker nor the planner: §8.2 step 5 assigns a
candidate INTO A SLOT, and a slot is a work row, so an `el` that answers `true` at a Wall, a
Routine or the wind-down is claiming step 5 might put a candidate there.  `WorkAnchored` is
that property of `el` and **nothing else**; `dayPlan_ok_on_a_quiet_day` is §6.1's dayPlan_ok
at eleven of eleven for every quiet request and every `WorkAnchored` eligibility.

**Say what it is worth, before a reader counts it.**  On a quiet day it is worth proof
coverage and NOT subject coverage, for the same reason W-20's tenth conjunct was: no row of a
quiet day is work (`dayPlan_has_no_work_row`), so a `WorkAnchored` `el` makes
`eligibleSomewhere` FALSE everywhere and all four eligibility-dependent conjuncts become
vacuous instead of one.  The census below is what measures that, and
`PlannerWit.the_quiet_eleven_is_one_checker_biting` computes it.  What the theorem
buys is not a bigger number: it is that **the residue of §6.1's lift on the quiet class is now
a named property of Planner.eligibleAt** that P5 can discharge in one line, instead of a
restatement of one of L26's eleven that P5 must refute first. -/

/-- **`el` never admits a candidate at a row §8.2 step 5 cannot assign into.**  A property of
the eligibility, not of the checkers, and the only thing `dayPlan_ok_on_a_quiet_day` asks of
it.  Planner.eligibleAt's body is P5's (design §6.3, §15); this names what the lift needs
that body to satisfy, so the obligation is in a type rather than in a comment. -/
def WorkAnchored (el : Eligible) : Prop :=
  ∀ (r : PlanReq) (d : DayPlan) (s : Seg) (i : Id), el r d s i = true → s.kind.isWork = true

/-- `eligibleSomewhere` is monotone in the eligibility. -/
theorem eligibleSomewhere_mono {a b : Eligible}
    (h : ∀ r d s i, a r d s i = true → b r d s i = true) (r : PlanReq) (d : DayPlan) (i : Id)
    (ha : eligibleSomewhere a r d i = true) : eligibleSomewhere b r d i = true := by
  simp only [eligibleSomewhere, List.any_eq_true] at ha ⊢
  obtain ⟨s, hs, hel⟩ := ha
  exact ⟨s, hs, h r d s.val i hel⟩

theorem monotoneInRank_antitone {a b : Eligible}
    (h : ∀ r d s i, a r d s i = true → b r d s i = true) (r : PlanReq) (d : DayPlan)
    (hb : monotoneInRank b r d = true) : monotoneInRank a r d = true := by
  refine List.all_eq_true.2 (fun i hi => List.all_eq_true.2 (fun j hj => ?_))
  have hbij : rankPairOk b r d i j = true :=
    List.all_eq_true.1 (List.all_eq_true.1 hb i hi) j hj
  refine (rankPairOk_iff a r d i j).2 (fun e f hgi hgj hp hc hdoc hr hei hej hmem => ?_)
  exact (rankPairOk_iff b r d i j).1 hbij e f hgi hgj hp hc hdoc hr
    (eligibleSomewhere_mono h r d i hei) (eligibleSomewhere_mono h r d j hej) hmem

theorem hotBeforeQueue_antitone {a b : Eligible}
    (h : ∀ r d s i, a r d s i = true → b r d s i = true) (r : PlanReq) (d : DayPlan)
    (hb : hotBeforeQueue b r d = true) : hotBeforeQueue a r d = true := by
  refine List.all_eq_true.2 (fun i hi => List.all_eq_true.2 (fun j hj => ?_))
  have hbij : hotPairOk b r d i j = true :=
    List.all_eq_true.1 (List.all_eq_true.1 hb i hi) j hj
  refine (hotPairOk_iff a r d i j).2 (fun e f hgi hgj hhot hnot hei sj hsj hj' => ?_)
  exact (hotPairOk_iff b r d i j).1 hbij e f hgi hgj hhot hnot
    (eligibleSomewhere_mono h r d i hei) sj hsj hj'

theorem impossibleKept_antitone {a b : Eligible}
    (h : ∀ r d s i, a r d s i = true → b r d s i = true) (r : PlanReq) (d : DayPlan)
    (hb : impossibleKept b r d = true) : impossibleKept a r d = true :=
  (impossibleKept_iff a r d).2 (fun p hp hel =>
    (impossibleKept_iff b r d).1 hb p hp (eligibleSomewhere_mono h r d p.1 hel))

theorem batchDoesNotReachPast_antitone {a b : Eligible}
    (h : ∀ r d s i, a r d s i = true → b r d s i = true) (r : PlanReq) (d : DayPlan)
    (hb : batchDoesNotReachPast b r d = true) : batchDoesNotReachPast a r d = true := by
  refine List.all_eq_true.2 (fun s hs => ?_)
  have hbs := List.all_eq_true.1 hb s hs
  cases hk : s.val.kind
  case batch ids =>
    rw [hk] at hbs
    refine List.all_eq_true.2 (fun i hi => List.all_eq_true.2 (fun j hj => ?_))
    have hbij : batchPairOk b r d s ids i j = true :=
      List.all_eq_true.1 (List.all_eq_true.1 hbs i hi) j hj
    refine (batchPairOk_iff a r d s ids i j).2 (fun e f hn hgi hgj hel hc hdoc hr => ?_)
    exact (batchPairOk_iff b r d s ids i j).1 hbij e f hn hgi hgj (h r d s.val j hel) hc hdoc hr
  all_goals rfl

/-- **§6.1's `planOk` is antitone in the eligibility.**  The four eligibility-dependent
checkers read `el` only in their antecedents, so narrowing `el` narrows what has to be
checked.  `planOkCore` does not mention `el` at all. -/
theorem planOk_antitone {a b : Eligible}
    (h : ∀ r d s i, a r d s i = true → b r d s i = true) (r : PlanReq) (d : DayPlan)
    (hb : planOk b r d = true) : planOk a r d = true := by
  have hcore : planOkCore r d = true := planOk_imp_core b r d hb
  have hrank : monotoneInRank b r d = true :=
    checks_all b r d hb ⟨.rank, monotoneInRank b⟩ (by simp [checksOf, checksEligible])
  have hhot : hotBeforeQueue b r d = true :=
    checks_all b r d hb ⟨.hot, hotBeforeQueue b⟩ (by simp [checksOf, checksEligible])
  have himp : impossibleKept b r d = true :=
    checks_all b r d hb ⟨.impossible, impossibleKept b⟩ (by simp [checksOf, checksEligible])
  have hbat : batchDoesNotReachPast b r d = true :=
    checks_all b r d hb ⟨.batch, batchDoesNotReachPast b⟩ (by simp [checksOf, checksEligible])
  simp only [planOk, checksOf, List.all_append, checksEligible, List.all_cons, List.all_nil,
    Bool.and_true, monotoneInRank_antitone h r d hrank, hotBeforeQueue_antitone h r d hhot,
    impossibleKept_antitone h r d himp, batchDoesNotReachPast_antitone h r d hbat]
  exact hcore

/-- **The `∀ el` axis collapses to one computation.**  `fun _ _ _ _ => true` — the
`PlannerWit.permissive` eligibility — is the top of the order `planOk_antitone` is about, so
the battery passing there is the battery passing at EVERY eligibility, Planner.eligibleAt
included whenever P5 writes it.

This is the converse of W-19's ceiling and the two together are an `↔`: a refutation at
`permissive` refutes the `∀ el` form (instantiate), and a proof at `permissive` proves it. -/
theorem planOk_at_every_eligibility (r : PlanReq) (d : DayPlan)
    (h : planOk (fun _ _ _ _ => true) r d = true) (el : Eligible) : planOk el r d = true :=
  planOk_antitone (fun _ _ _ _ _ => rfl) r d h

/-- **No row of a quiet day is work.**  Strictly stronger than
`dayPlan_assigns_nothing_on_a_quiet_day`, which it now proves: `SegKind.isWork` is `Block` and
`Batch` and nothing else, `dayPlan_has_no_block_row` kills the first and
`the_day_has_no_batch_row` the second. -/
theorem dayPlan_has_no_work_row (r : PlanReq)
    (hnopast : ∀ t ∈ pastRows r, t.kind ≠ SegKind.block)
    (hnorun : r.activeRun = none) :
    ∀ s ∈ (dayPlan r).segments, s.val.kind.isWork = false := by
  intro s hs
  have hnb : ∀ ids, s.val.kind ≠ SegKind.batch ids := the_day_has_no_batch_row r s hs
  have hnbl : s.val.kind ≠ SegKind.block := dayPlan_has_no_block_row r hnopast hnorun s hs
  cases hk : s.val.kind <;> first
    | exact absurd hk hnbl
    | exact absurd hk (hnb _)
    | rfl

/-- A `WorkAnchored` eligibility admits nothing at all on a day with no work row. -/
theorem eligibleSomewhere_of_no_work_row {el : Eligible} (hw : WorkAnchored el) (r : PlanReq)
    (d : DayPlan) (hno : ∀ s ∈ d.segments, s.val.kind.isWork = false) (i : Id) :
    eligibleSomewhere el r d i = false := by
  refine Bool.eq_false_iff.2 (fun h => ?_)
  simp only [eligibleSomewhere, List.any_eq_true] at h
  obtain ⟨s, hs, hel⟩ := h
  exact absurd ((hw r d s.val i hel).symm.trans (hno s hs)) (by simp)

theorem monotoneInRank_of_nothing_eligible (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : ∀ i, eligibleSomewhere el r d i = false) : monotoneInRank el r d = true := by
  refine List.all_eq_true.2 (fun i _ => List.all_eq_true.2 (fun j _ => ?_))
  refine (rankPairOk_iff el r d i j).2 (fun e f _ _ _ _ _ _ hei _ _ => ?_)
  exact absurd (hei.symm.trans (h i)) (by simp)

theorem hotBeforeQueue_of_nothing_eligible (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : ∀ i, eligibleSomewhere el r d i = false) : hotBeforeQueue el r d = true := by
  refine List.all_eq_true.2 (fun i _ => List.all_eq_true.2 (fun j _ => ?_))
  refine (hotPairOk_iff el r d i j).2 (fun e f _ _ _ _ hei _ _ _ => ?_)
  exact absurd (hei.symm.trans (h i)) (by simp)

theorem impossibleKept_of_nothing_eligible (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : ∀ i, eligibleSomewhere el r d i = false) : impossibleKept el r d = true :=
  (impossibleKept_iff el r d).2 (fun p _ hel => absurd (hel.symm.trans (h p.1)) (by simp))

/-- **ELEVEN of §6.1's eleven, over the WHOLE day, at every `WorkAnchored` eligibility.**
Design §6.1's dayPlan_ok, for the class W-20 left at ten.  The hypotheses are W-20's quiet
class unchanged — a log with no Block for today and nothing running — plus one property of
`el`, and `WorkAnchored`'s doc comment says why that property is step 5's own and not a
weakening of any checker.

**The four eligibility-dependent conjuncts are all vacuous here** and
`PlannerWit.the_quiet_eleven_is_one_checker_biting` computes that; see the section
header before quoting "eleven of eleven" as eleven checkers biting. -/
theorem dayPlan_ok_on_a_quiet_day (el : Eligible) (r : PlanReq)
    (hagree : r.wallsAgree = true)
    (hactive : r.activeAgrees = true)
    (hday : r.dayAgrees = true)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd)
    (hnopast : ∀ t ∈ pastRows r, t.kind ≠ SegKind.block)
    (hnorun : r.activeRun = none)
    (hplain : ∀ (i : Id) (e : Entity) (a b : Field.DT),
      r.plan.val.store.get i = some e → e.val.shape = Shape.interval a b →
      e.val.buffer = none ∧
        r.dayStart ≤ (Cal.instantOf r.tz a.day a.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec ≤ r.dayEnd ∧
        (Cal.instantOf r.tz a.day a.time).sec < (Cal.instantOf r.tz b.day b.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec < LogStamp.yearEnd)
    (hwork : WorkAnchored el) :
    planOk el r (dayPlan r) = true := by
  have hnone : ∀ i, eligibleSomewhere el r (dayPlan r) i = false :=
    eligibleSomewhere_of_no_work_row hwork r _ (dayPlan_has_no_work_row r hnopast hnorun)
  refine dayPlan_ok_on_a_quiet_day_given_hot el r hagree hactive hday hnowcal hnopast hnorun
    hplain ?_
  exact hotBeforeQueue_of_nothing_eligible el r _ hnone

/-! ############################################################################
## The subject census, as a function of the battery's own list (W-21)
############################################################################

**The problem this ends.**  Three runs have shipped a sentence of the form "N of the eleven",
and they were counting different things over different requests: W-18's **seven of eleven have
a subject at `theCensusRequest`**, W-19's **nine of eleven conjuncts proved at every
eligibility**, W-20's **ten of eleven on the quiet class**.  Two of those are proof coverage
and one is subject coverage, and a reader who takes either for the other over-counts by the
whole of design §6.4's remaining work (README gaps 650, 684, 852, 961).

Proof coverage already has a compiler-checked count: `checksOf_length` and the lift theorems
assemble `planOk` itself rather than a transcription of it.  **Subject coverage did not**: it
was a prose table in `PlannerWit.lean` beside an eleven-way `decide`, and the "seven" was a
reader's count of the table's `yes` rows.  `subjectOf` and `subjectCount` are that count,
keyed on the checker's OWN `CheckName`, filtered over `checksOf`'s OWN list — so there is no
second list to fall out of step with the first, and no transcription to miscount.

**What a subject is here.**  Each checker is an implication (or, for `overbook`, a sum), and
its subject is the population its ANTECEDENT admits — exactly the idiom
`rankSubjects`/`hotSubjects` already used for the two comparisons.  `subjectOf` spells each
antecedent and none of any conclusion, so no bug in it can make a checker pass;
`a_check_with_no_subject_is_a_free_pass` is the theorem that makes it mean something, and
`planOk_of_no_subject` is the honest statement of what a battery with an empty census is worth
— which is nothing. -/

/-- The pairs `rankPairOk`'s implication is **about** at `el`, `r` and `d`: every antecedent
of the checker, and none of its conclusion.  (`PlannerWit`'s until W-21 — see the note there.)
-/
def rankSubjects (el : Eligible) (r : PlanReq) (d : DayPlan) : List (Id × Id) :=
  r.plan.val.store.dom.flatMap (fun i => r.plan.val.store.dom.filterMap (fun j =>
    match r.plan.val.store.get i, r.plan.val.store.get j with
    | some e, some f =>
        if decide (rootPrio r.plan.val i = rootPrio r.plan.val j)
             && decide (effectiveCi r.plan.val i = effectiveCi r.plan.val j)
             && decide (e.val.live.doc = f.val.live.doc)
             && decide (e.val.live.rank < f.val.live.rank)
             && eligibleSomewhere el r d i && eligibleSomewhere el r d j
             && decide (j ∈ assignedOf d)
        then some (i, j) else none
    | _, _ => none))

/-- The pairs `hotPairOk`'s implication is **about**: a hot `i`, a not-hot `j` that some row
of the day carries, and `i` eligible somewhere. -/
def hotSubjects (el : Eligible) (r : PlanReq) (d : DayPlan) : List (Id × Id) :=
  r.plan.val.store.dom.flatMap (fun i => r.plan.val.store.dom.filterMap (fun j =>
    match r.plan.val.store.get i, r.plan.val.store.get j with
    | some e, some f =>
        if decide (Flag.hot ∈ e.val.flags) && decide (Flag.hot ∉ f.val.flags)
             && eligibleSomewhere el r d i
             && d.segments.any (fun s => s.val.item == some j)
        then some (i, j) else none
    | _, _ => none))

/-- **Does this checker's quantifier have anything to range over on this day?**  One case per
`CheckName`, each spelling that checker's ANTECEDENT and nothing else. -/
def subjectOf (el : Eligible) (n : CheckName) (r : PlanReq) (d : DayPlan) : Bool :=
  match n with
  | .overbook => (withoutActive r d).segments.any (fun s => s.val.kind == SegKind.block)
  | .oneBlock => d.segments.any (fun s => s.val.kind == SegKind.block)
  | .energyFilter =>
      d.segments.any (fun s => !isActive r s && s.val.kind == SegKind.block
        && s.val.item.isSome && s.val.energy.isSome)
  | .overWall =>
      d.segments.any (fun s => s.val.kind == SegKind.block)
        && d.segments.any (fun s => s.val.kind == SegKind.wall)
  | .overBreak =>
      d.segments.any (fun s => s.val.kind == SegKind.block)
        && d.segments.any (fun s => s.val.kind == SegKind.brk)
  | .windDown =>
      d.segments.any (fun b => b.val.kind == SegKind.block && b.val.item.isSome
        && d.segments.any (fun w => w.val.kind == SegKind.windDown
            && decide (w.val.start ≤ b.val.start)))
  | .wallMoved =>
      d.segments.any (fun s => s.val.kind == SegKind.wall &&
        (match s.val.item with
         | none => false
         | some i =>
             match r.plan.val.store.get i with
             | none => false
             | some e =>
                 match e.val.shape with
                 | Shape.interval _ _ => true
                 | _ => false))
  | .rank => !(rankSubjects el r d).isEmpty
  | .hot => !(hotSubjects el r d).isEmpty
  | .impossible => d.diagnostics.impossible.val.any (fun p => eligibleSomewhere el r d p.1)
  | .batch =>
      d.segments.any (fun s =>
        match s.val.kind with
        | SegKind.batch ids =>
            ids.val.any (fun i => r.plan.val.store.dom.any (fun j =>
              !decide (j ∈ ids.val) &&
                (match r.plan.val.store.get i, r.plan.val.store.get j with
                 | some e, some f =>
                     el r d s.val j
                       && decide (effectiveCi r.plan.val i = effectiveCi r.plan.val j)
                       && decide (e.val.live.doc = f.val.live.doc)
                       && decide (f.val.live.rank < e.val.live.rank)
                 | _, _ => false)))
        | _ => false)

/-- **The ratio, as the compiler's arithmetic over `checksOf`'s own list.**  The filter is
keyed on each check's own `name`, so the count cannot drift from the battery it is about the
way a parallel table can. -/
def subjectCount (el : Eligible) (r : PlanReq) (d : DayPlan) : Nat :=
  ((checksOf el).filter (fun c => subjectOf el c.name r d)).length

/-! ### An empty subject is a free pass, checker by checker

Eleven lemmas and one theorem over `checksOf`'s own list.  Without them `subjectOf` would be
eleven opinions about what a quantifier ranges over; with them it is a **sufficient condition
for the checker to answer `true` for no reason at all**, which is the thing AGENTS §9.2 calls
a check no input can fail and which §5.2 calls a theorem that compiles and means nothing. -/

/-- The dual of `all_eq_false_of_mem`: nothing in the list satisfies a `false` `any`. -/
theorem false_of_any_eq_false {α : Type} {l : List α} {p : α → Bool} (h : l.any p = false)
    {x : α} (hx : x ∈ l) : p x = false := by
  cases hp : p x with
  | false => rfl
  | true => exact absurd (List.any_eq_true.2 ⟨x, hx, hp⟩) (by simp [h])

theorem blockSeconds_of_no_block (d : DayPlan)
    (h : d.segments.any (fun s => s.val.kind == SegKind.block) = false) :
    blockSeconds d = 0 := by
  have hnil : d.segments.filter (fun s => decide (s.val.kind = SegKind.block)) = [] := by
    refine List.filter_eq_nil_iff.2 (fun s hs => ?_)
    have := false_of_any_eq_false h hs
    simpa using this
  unfold blockSeconds
  rw [hnil]
  rfl

theorem noOverbook_of_no_subject (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : subjectOf el .overbook r d = false) : noOverbook r d = true := by
  simp only [subjectOf] at h
  simp [noOverbook, blockSeconds_of_no_block _ h]

theorem oneBlockAtATime_of_no_subject (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : subjectOf el .oneBlock r d = false) : oneBlockAtATime r d = true := by
  simp only [subjectOf] at h
  refine (oneBlockAtATime_iff r d).2 (fun s hs hk => ?_)
  have := false_of_any_eq_false h hs
  simp [hk] at this

theorem energyFilterOk_of_no_subject (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : subjectOf el .energyFilter r d = false) : energyFilterOk r d = true := by
  simp only [subjectOf] at h
  refine (energyFilterOk_iff r d).2 (fun s hs i lvl ha hk hi he => ?_)
  have := false_of_any_eq_false h hs
  simp [ha, hk, hi, he] at this

theorem noBlockOverAWall_of_no_subject (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : subjectOf el .overWall r d = false) : noBlockOverAWall r d = true := by
  simp only [subjectOf, Bool.and_eq_false_iff] at h
  refine (noBlockOverAWall_iff r d).2 (fun b hb w hw hkb hkw => ?_)
  rcases h with h | h
  · have := false_of_any_eq_false h hb; simp [hkb] at this
  · have := false_of_any_eq_false h hw; simp [hkw] at this

theorem noBlockOverABreak_of_no_subject (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : subjectOf el .overBreak r d = false) : noBlockOverABreak r d = true := by
  simp only [subjectOf, Bool.and_eq_false_iff] at h
  refine (noBlockOverABreak_iff r d).2 (fun b hb k hk hkb hkk => ?_)
  rcases h with h | h
  · have := false_of_any_eq_false h hb; simp [hkb] at this
  · have := false_of_any_eq_false h hk; simp [hkk] at this

theorem noDemandingAfterWindDown_of_no_subject (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : subjectOf el .windDown r d = false) : noDemandingAfterWindDown r d = true := by
  simp only [subjectOf] at h
  refine (noDemandingAfterWindDown_iff r d).2 (fun b hb w hw i hi hkb hkw hle => ?_)
  have hbf := false_of_any_eq_false h hb
  have hwt : (d.segments.any (fun w => w.val.kind == SegKind.windDown
      && decide (w.val.start ≤ b.val.start))) = true :=
    List.any_eq_true.2 ⟨w, hw, by simp [hkw, hle]⟩
  simp [hkb, hi, hwt] at hbf

theorem wallsUnmoved_of_no_subject (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : subjectOf el .wallMoved r d = false) : wallsUnmoved r d = true := by
  simp only [subjectOf] at h
  refine (wallsUnmoved_iff r d).2 (fun s hs i e a b hi hg hsh hk => ?_)
  have := false_of_any_eq_false h hs
  simp [hk, hi, hg, hsh] at this

/-- `(i, j)` is in `rankSubjects` exactly when `rankPairOk`'s antecedents all hold of it. -/
theorem mem_rankSubjects (el : Eligible) (r : PlanReq) (d : DayPlan) {i j : Id} {e f : Entity}
    (hi : i ∈ r.plan.val.store.dom) (hj : j ∈ r.plan.val.store.dom)
    (hgi : r.plan.val.store.get i = some e) (hgj : r.plan.val.store.get j = some f)
    (hp : rootPrio r.plan.val i = rootPrio r.plan.val j)
    (hc : effectiveCi r.plan.val i = effectiveCi r.plan.val j)
    (hdoc : e.val.live.doc = f.val.live.doc) (hr : e.val.live.rank < f.val.live.rank)
    (hei : eligibleSomewhere el r d i = true) (hej : eligibleSomewhere el r d j = true)
    (hmem : j ∈ assignedOf d) : (i, j) ∈ rankSubjects el r d := by
  refine List.mem_flatMap.2 ⟨i, hi, List.mem_filterMap.2 ⟨j, hj, ?_⟩⟩
  simp [hgi, hgj, hp, hc, hdoc, hr, hei, hej, hmem]

/-- `(i, j)` is in `hotSubjects` exactly when `hotPairOk`'s antecedents all hold of it. -/
theorem mem_hotSubjects (el : Eligible) (r : PlanReq) (d : DayPlan) {i j : Id} {e f : Entity}
    (hi : i ∈ r.plan.val.store.dom) (hj : j ∈ r.plan.val.store.dom)
    (hgi : r.plan.val.store.get i = some e) (hgj : r.plan.val.store.get j = some f)
    (hhot : Flag.hot ∈ e.val.flags) (hnot : Flag.hot ∉ f.val.flags)
    (hei : eligibleSomewhere el r d i = true)
    (hrow : d.segments.any (fun s => s.val.item == some j) = true) :
    (i, j) ∈ hotSubjects el r d := by
  refine List.mem_flatMap.2 ⟨i, hi, List.mem_filterMap.2 ⟨j, hj, ?_⟩⟩
  simp [hgi, hgj, hhot, hnot, hei, hrow]

theorem monotoneInRank_of_no_subject (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : subjectOf el .rank r d = false) : monotoneInRank el r d = true := by
  simp only [subjectOf] at h
  have hnil : rankSubjects el r d = [] := by
    cases hx : rankSubjects el r d with
    | nil => rfl
    | cons a t => rw [hx] at h; simp at h
  refine List.all_eq_true.2 (fun i hi => List.all_eq_true.2 (fun j hj => ?_))
  refine (rankPairOk_iff el r d i j).2 (fun e f hgi hgj hp hc hdoc hr hei hej hmem => ?_)
  have := mem_rankSubjects el r d hi hj hgi hgj hp hc hdoc hr hei hej hmem
  rw [hnil] at this
  exact absurd this (by simp)

theorem hotBeforeQueue_of_no_subject (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : subjectOf el .hot r d = false) : hotBeforeQueue el r d = true := by
  simp only [subjectOf] at h
  have hnil : hotSubjects el r d = [] := by
    cases hx : hotSubjects el r d with
    | nil => rfl
    | cons a t => rw [hx] at h; simp at h
  refine List.all_eq_true.2 (fun i hi => List.all_eq_true.2 (fun j hj => ?_))
  refine (hotPairOk_iff el r d i j).2 (fun e f hgi hgj hhot hnot hei sj hsj hij => ?_)
  have hrow : d.segments.any (fun s => s.val.item == some j) = true :=
    List.any_eq_true.2 ⟨sj, hsj, by simp [hij]⟩
  have := mem_hotSubjects el r d hi hj hgi hgj hhot hnot hei hrow
  rw [hnil] at this
  exact absurd this (by simp)

theorem impossibleKept_of_no_subject (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : subjectOf el .impossible r d = false) : impossibleKept el r d = true := by
  simp only [subjectOf] at h
  refine (impossibleKept_iff el r d).2 (fun p hp hel => ?_)
  have := false_of_any_eq_false h hp
  simp [hel] at this

theorem batchDoesNotReachPast_of_no_subject (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : subjectOf el .batch r d = false) : batchDoesNotReachPast el r d = true := by
  simp only [subjectOf] at h
  refine List.all_eq_true.2 (fun s hs => ?_)
  have hsf := false_of_any_eq_false h hs
  cases hk : s.val.kind
  case batch ids =>
    rw [hk] at hsf
    refine List.all_eq_true.2 (fun i hi => List.all_eq_true.2 (fun j hj => ?_))
    refine (batchPairOk_iff el r d s ids i j).2 (fun e f hn hgi hgj hel hc hdoc hr => ?_)
    have hin : (ids.val.any (fun i => r.plan.val.store.dom.any (fun j =>
        !decide (j ∈ ids.val) &&
          (match r.plan.val.store.get i, r.plan.val.store.get j with
           | some e, some f =>
               el r d s.val j
                 && decide (effectiveCi r.plan.val i = effectiveCi r.plan.val j)
                 && decide (e.val.live.doc = f.val.live.doc)
                 && decide (f.val.live.rank < e.val.live.rank)
           | _, _ => false)))) = true :=
      List.any_eq_true.2 ⟨i, hi, List.any_eq_true.2 ⟨j, hj, by
        simp [hn, hgi, hgj, hel, hc, hdoc, hr]⟩⟩
    simp [hin] at hsf
  all_goals rfl

/-- **A checker whose subject is empty answers `true` for no reason at all.**  This is what
makes `subjectCount` a measurement rather than eleven opinions: below the census a `true` is
free, and `checksOf` is the list both sides range over. -/
theorem a_check_with_no_subject_is_a_free_pass (el : Eligible) (r : PlanReq) (d : DayPlan) :
    ∀ c ∈ checksOf el, subjectOf el c.name r d = false → c.run r d = true := by
  intro c hc h
  simp only [checksOf, checksCore, checksEligible, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with (rfl|rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl)
  · exact noOverbook_of_no_subject el r d h
  · exact oneBlockAtATime_of_no_subject el r d h
  · exact energyFilterOk_of_no_subject el r d h
  · exact noBlockOverAWall_of_no_subject el r d h
  · exact noBlockOverABreak_of_no_subject el r d h
  · exact noDemandingAfterWindDown_of_no_subject el r d h
  · exact wallsUnmoved_of_no_subject el r d h
  · exact monotoneInRank_of_no_subject el r d h
  · exact hotBeforeQueue_of_no_subject el r d h
  · exact impossibleKept_of_no_subject el r d h
  · exact batchDoesNotReachPast_of_no_subject el r d h

/-- **A battery with an empty census passes, and is worth nothing.**  `planOk` answering
`true` at a request where `subjectCount` is `0` is eleven empty quantifiers, and this theorem
is the statement of that in the compiler rather than in a comment.  It is also the D40 witness
for `subjectOf`: folded to `fun _ _ _ _ => false` this proof would make `planOk` unconditional
and `planOk_can_fail` refutes that. -/
theorem planOk_of_no_subject (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : subjectCount el r d = 0) : planOk el r d = true := by
  have hempty : (checksOf el).filter (fun c => subjectOf el c.name r d) = [] :=
    List.eq_nil_of_length_eq_zero h
  refine List.all_eq_true.2 (fun c hc => ?_)
  refine a_check_with_no_subject_is_a_free_pass el r d c hc ?_
  cases hsub : subjectOf el c.name r d with
  | false => rfl
  | true =>
      have : c ∈ (checksOf el).filter (fun c => subjectOf el c.name r d) :=
        List.mem_filter.2 ⟨hc, hsub⟩
      rw [hempty] at this
      exact absurd this (by simp)

/-- The census is over the battery's own list, so it cannot exceed it. -/
theorem subjectCount_le_eleven (el : Eligible) (r : PlanReq) (d : DayPlan) :
    subjectCount el r d ≤ 11 := by
  have := List.length_filter_le (fun c => subjectOf el c.name r d) (checksOf el)
  rw [checksOf_length el] at this
  exact this

/-! ### The census's own ceiling: SEVEN, proved, not surveyed

The four vacuity theorems above say four checkers cannot FAIL on a day `Planner.dayPlan`
produces.  The four below say something the census needs and they did not: that those four
checkers have **no subject at all**, at every request and at every eligibility.  The
difference is the difference between "it passes" and "there is nothing for it to pass" — it is
exactly the distinction this whole section exists to keep, and until now the "and none can"
column of `PlannerWit`'s census table was prose beside an eleven-way `decide` at one request.

`the_census_ceiling_is_seven` is what they buy: **no `PlanReq` whatever can put more than
seven of the eleven in play today**, so the seven `PlannerWit.the_census_ratio` computes at
`theCensusRequest` is a ceiling that has been reached and not a high-water mark that a future
witness might beat.  The four that cannot reach it are design §6.4's P5, P5/P7 and P8 rows,
and they are the same four either way round. -/

theorem energyFilter_has_no_subject (el : Eligible) (r : PlanReq) :
    subjectOf el .energyFilter r (dayPlan r) = false := by
  simp only [subjectOf]
  refine Bool.eq_false_iff.2 (fun h => ?_)
  obtain ⟨s, hs, hp⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨-, hk⟩, -⟩, hen⟩ := hp
  rw [no_block_row_of_the_day_carries_a_slot_energy r s hs hk] at hen
  simp at hen

theorem windDown_has_no_subject (el : Eligible) (r : PlanReq)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd) :
    subjectOf el .windDown r (dayPlan r) = false := by
  simp only [subjectOf]
  refine Bool.eq_false_iff.2 (fun h => ?_)
  obtain ⟨b, hb, hp⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨hbk, -⟩, hany⟩ := hp
  obtain ⟨w, hw, hwp⟩ := List.any_eq_true.1 hany
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hwp
  have := no_block_row_of_the_day_reaches_the_wind_down r hnowcal b w hb hw hbk hwp.1
  omega

theorem batch_has_no_subject (el : Eligible) (r : PlanReq) :
    subjectOf el .batch r (dayPlan r) = false := by
  simp only [subjectOf]
  refine Bool.eq_false_iff.2 (fun h => ?_)
  obtain ⟨s, hs, hp⟩ := List.any_eq_true.1 h
  cases hk : s.val.kind
  case batch ids => exact absurd hk (the_day_has_no_batch_row r s hs ids)
  all_goals (rw [hk] at hp; simp at hp)

theorem impossible_has_no_subject (el : Eligible) (r : PlanReq) :
    subjectOf el .impossible r (dayPlan r) = false := by
  simp only [subjectOf, the_day_names_no_impossible_item r, List.any_nil]

/-- **Seven is the ceiling of the census, for every request and every eligibility.**  Four of
`checksOf`'s eleven have an empty subject on every day `Planner.dayPlan` produces, so the
filter `subjectCount` runs can keep at most the other seven.  P5's fold ends it for
`energyFilter` and `batch`, P5/P7 for `windDown`, P8 for `impossible` (design §6.4). -/
theorem the_census_ceiling_is_seven (el : Eligible) (r : PlanReq)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd) :
    subjectCount el r (dayPlan r) ≤ 7 := by
  have e1 := energyFilter_has_no_subject el r
  have e2 := windDown_has_no_subject el r hnowcal
  have e3 := batch_has_no_subject el r
  have e4 := impossible_has_no_subject el r
  show (List.filter (fun c => subjectOf el c.name r (dayPlan r)) (checksOf el)).length ≤ 7
  have hcore : checksCore.filter (fun c => subjectOf el c.name r (dayPlan r))
      = ([⟨.overbook, noOverbook⟩, ⟨.oneBlock, oneBlockAtATime⟩,
          ⟨.overWall, noBlockOverAWall⟩, ⟨.overBreak, noBlockOverABreak⟩,
          ⟨.wallMoved, wallsUnmoved⟩] : List Check).filter
            (fun c => subjectOf el c.name r (dayPlan r)) := by
    simp only [checksCore, List.filter_cons, e1, e2, Bool.false_eq_true, if_false]
  have helig : (checksEligible el).filter (fun c => subjectOf el c.name r (dayPlan r))
      = ([⟨.rank, monotoneInRank el⟩, ⟨.hot, hotBeforeQueue el⟩] : List Check).filter
            (fun c => subjectOf el c.name r (dayPlan r)) := by
    simp only [checksEligible, List.filter_cons, e3, e4, Bool.false_eq_true, if_false]
  rw [checksOf, List.filter_append, List.length_append, hcore, helig]
  have b1 := List.length_filter_le (fun c => subjectOf el c.name r (dayPlan r))
    ([⟨.overbook, noOverbook⟩, ⟨.oneBlock, oneBlockAtATime⟩,
      ⟨.overWall, noBlockOverAWall⟩, ⟨.overBreak, noBlockOverABreak⟩,
      ⟨.wallMoved, wallsUnmoved⟩] : List Check)
  have b2 := List.length_filter_le (fun c => subjectOf el c.name r (dayPlan r))
    ([⟨.rank, monotoneInRank el⟩, ⟨.hot, hotBeforeQueue el⟩] : List Check)
  simp only [List.length_cons, List.length_nil] at b1 b2
  omega

/-! ############################################################################
## W-22: ELEVEN of eleven over the rows §8.3 is about, at EVERY request
############################################################################

W-20 reached ten over the whole day on the *quiet* class; W-21 reached eleven on the same
class, for every `WorkAnchored` eligibility.  **Both are statements about a class of
requests**, and the class has exactly one inhabitant in this kernel's whole witness set
(`PlannerWit.theQuietCensusRequest`): `hnorun` — *nothing is running* — and `hnopast` — *the
log holds no Block for today* — are both false at every other request the module builds.

This section drops **both** hypotheses.  What replaces them is not a weaker checker and not a
larger class assumption: it is the day W-17 already named.  `withoutPast` keeps the rows §8.3's
laws are about — the work rows that start at or after `now`, and every non-work comparand —
and `a_block_row_from_now_is_the_reservation` says, **for every request and with nothing
assumed about the log**, that a Block row surviving that filter is §8.2 choice 5b's
reservation.  `the_day_has_no_batch_row` says the same of the other work kind.  So *every work
row of `withoutPast`'s day is the reservation*, at every request, and the four
eligibility-dependent conjuncts collapse for a reason that is a property of §8.2 step 5's own
filter rather than of the day.

**`SlotAnchored` is that property and it is one clause longer than `WorkAnchored`.**  §8.2
step 5 assigns a candidate into a **free** slot; the reservation is the row choice 5b takes
*out* of the slot supply before the fold runs ("the running block takes no slot at all",
design §6.3 row 2).  An `el` answering `true` there is claiming step 5 might assign into the
row it was told not to.  README gap 960 offered exactly this as repair **(a)** and W-21 could
not use it, because *"no reservation exists on a quiet day"*.  Off the quiet class it is the
repair that works, and nothing else has to move.

**What it is worth, and the number is FOUR.**  The four eligibility-dependent conjuncts are
vacuous here, as they are on the quiet class — but three more of the seven core checks have a
subject than did there, and `overbook` loses one it had on the whole day, because
`withoutActive` removes the only Block `withoutPast` leaves.
`the_census_ceiling_from_now_is_four` proves the exact ceiling: **at most four** of the eleven
can have a subject on this day at a `SlotAnchored` eligibility, at any request whatever, and
`PlannerWit.the_eleven_from_now_is_four_checkers_biting` reaches it.  Four is not seven: the
whole-day ceiling `the_census_ceiling_is_seven` counts `overbook` and the two comparisons,
and every one of those three is counted there **because of the replayed past**, which is the
half of the day §8.3 is not about.  Neither number is the other's correction; they are
ceilings on two different days and each says which.

### THE ONE NUMBER, AND WHICH QUESTION IT ANSWERS

Four runs of this campaign have shipped a bare *"N of the eleven"*, and the reason they
disagreed is that **there are three questions and a number is meaningless without its three
coordinates** — which day, which class of request, which eligibility.  This is the repo's
single statement of them, and every other sentence about the ratio points here.

| the question | what counts it | today's answer, with its coordinates |
|---|---|---|
| how many of the eleven are **proved** | a lift theorem assembling `planOk` over `checksOf`'s own list | **eleven** on `withoutPast`'s day, every request, every `SlotAnchored` `el` (`dayPlan_ok_from_now`); **eleven** on the whole day for the quiet class at every `WorkAnchored` `el` (`dayPlan_ok_on_a_quiet_day`); **nine** on `withoutPast`'s day at *every* `el` (`dayPlan_ok_from_now_except_the_two_comparisons`); **the seven core checks** on the whole day, every request, every `FromNowAnchored` `el` (`dayPlan_ok_is_the_core_seven`, W-23) — and the eleven there is **refuted** at a merely `SlotAnchored` one (`PlannerWit.dayPlan_ok_on_the_whole_day_at_a_slot_anchored_eligibility_is_refuted`) |
| how many have **anything to range over** | `subjectCount` over `checksOf`'s own list | ceiling **seven**, whole day, every request, every `el` (`the_census_ceiling_is_seven`), reached at `PlannerWit.theCensusRequest`; ceiling **four** on `withoutPast`'s day at every `SlotAnchored` `el` (`the_census_ceiling_from_now_is_four`), reached at the same request; ceiling **five**, whole day, every request, every `FromNowAnchored` `el` (`the_census_ceiling_on_the_whole_day_is_five`, W-23), reached at the same request again |
| how many **bite inside a proved lift** | the census evaluated at the lift's own arguments | **one** on the quiet class (`PlannerWit.the_quiet_eleven_is_one_checker_biting`); **four** at the census request on `withoutPast`'s day (`PlannerWit.the_eleven_from_now_is_four_checkers_biting`); **five** at the same request on the whole day at a `FromNowAnchored` `el` (`PlannerWit.the_whole_day_census_at_the_from_now_eligibility_is_five`, W-23) |

**W-23 added the fourth coordinate — the whole day at a `FromNowAnchored` eligibility — and
moved no number in the three that were here.**  Its row is five, and five is what a hypothesis
on the eligibility costs in subjects on the day that already had seven; the headline below is
unchanged by it.

**The honest headline is the SUBJECT count and the number is SEVEN.**  A conjunct can be
proved by emptiness — four of the eleven are, at every request, and `a_check_with_no_subject_is_a_free_pass`
is the theorem that says so — so the proof count is the number most likely to be read for more
than it is.  Seven is the one figure that is a **ceiling over every request and every
eligibility** on the day the planner actually produces, and it is *not an achievement*: it is
the measure of how much of the battery the stage has given anything to do.  **Four is the same
figure on the smaller day**, and it is smaller because the day is smaller, not because
anything regressed — `overbook`, `rank` and `hot` are the three it loses, and every one of them
is counted in the seven *because of the replayed past*.

**The fold induction design §6.2 prices at ≈ 4,500 lines is still not started, and this is not
a down payment on it.**  `Planner.dayRows`'s own doc comment is the record: the Block and
Batch rows of §8.2 step 5 are **not in the day** — they are the switch-shaped change (D19)
that makes the four emptiness theorems above false and takes `dayPlan_ok_core`'s `hblk` with
them.  Everything proved here is proved *because* those rows are absent.  `hblk` holding and
"the fold induction has its subject" are the same sentence with opposite signs. -/

/-- **An eligibility that admits a candidate only where §8.2 step 5 could put one**: at a work
row (`WorkAnchored`, W-21), and **not** at §8.2 choice 5b's reservation, which step 5 never
sees because choice 5b removes it from the slot supply before the fold runs.

`WorkAnchored` is reused rather than re-spelled (AGENTS §5.3) and `isActive` is the kernel's
one reader of *"is this row the running block's"*, so this predicate introduces no second
reading of either half.  Planner.eligibleAt's body is P5's; this is the second of the two
lines P5 owes the lift, and `PlannerWit.onlyOnFreeWorkRows` is the concrete instance that
fires it today. -/
def SlotAnchored (el : Eligible) : Prop :=
  WorkAnchored el ∧
    ∀ (r : PlanReq) (d : DayPlan) (s : WfSeg) (i : Id),
      el r d s.val i = true → isActive r s = false

/-- **Every work row of `withoutPast`'s day is §8.2 choice 5b's reservation**, at every
request and with nothing assumed about the log.  This is the whole content of the section:
`dayPlan_has_no_work_row` needed `hnopast` *and* `hnorun` to say a weaker thing (there are no
work rows at all); this says the rows that exist are all one row. -/
theorem withoutPast_work_rows_are_the_reservation (r : PlanReq) (s : WfSeg)
    (hs : s ∈ (withoutPast r (dayPlan r)).segments) (hw : s.val.kind.isWork = true) :
    isActive r s = true := by
  obtain ⟨hs', hnow⟩ := mem_withoutPast r _ s hs
  have hnb : ∀ ids, s.val.kind ≠ SegKind.batch ids := the_day_has_no_batch_row r s hs'
  have hk : s.val.kind = SegKind.block := by
    cases hkk : s.val.kind <;> rw [hkk] at hw <;>
      first
        | rfl
        | exact absurd hkk (hnb _)
        | simp [SegKind.isWork] at hw
  obtain ⟨t, ht, rfl⟩ := a_block_row_from_now_is_the_reservation r s hs' hk (hnow hw)
  obtain ⟨a, hai, hti⟩ := the_reservation_row_names_the_running_item r t ht
  unfold isActive
  rw [hai, segOf_item, hti]
  simp

/-- **The same, over the WHOLE day, for a log that holds no Block for today.**  W-21's quiet
class asked for `hnorun` on top of `hnopast`; this asks only for `hnopast`, and says the work
rows that do exist are the reservation rather than that none exists. -/
theorem dayPlan_work_rows_are_the_reservation (r : PlanReq)
    (hnopast : ∀ t ∈ pastRows r, t.kind ≠ SegKind.block) (s : WfSeg)
    (hs : s ∈ (dayPlan r).segments) (hw : s.val.kind.isWork = true) : isActive r s = true := by
  have hnb : ∀ ids, s.val.kind ≠ SegKind.batch ids := the_day_has_no_batch_row r s hs
  have hk : s.val.kind = SegKind.block := by
    cases hkk : s.val.kind <;> rw [hkk] at hw <;>
      first
        | rfl
        | exact absurd hkk (hnb _)
        | simp [SegKind.isWork] at hw
  obtain ⟨t, ht, rfl⟩ := dayPlan_block_rows_are_the_reservation r hnopast s hs hk
  obtain ⟨a, hai, hti⟩ := the_reservation_row_names_the_running_item r t ht
  unfold isActive
  rw [hai, segOf_item, hti]
  simp

/-- **A `SlotAnchored` eligibility admits nothing at all on a day whose only work row is the
reservation.**  Stated over an arbitrary `DayPlan` and an arbitrary "every work row is the
reservation" hypothesis, so the whole day and `withoutPast`'s get it from one proof — the
shape `monotoneInRank_of_nothing_assigned` already uses. -/
theorem eligibleSomewhere_of_only_the_reservation {el : Eligible} (hsl : SlotAnchored el)
    (r : PlanReq) (d : DayPlan)
    (hres : ∀ s ∈ d.segments, s.val.kind.isWork = true → isActive r s = true) (i : Id) :
    eligibleSomewhere el r d i = false := by
  refine Bool.eq_false_iff.2 (fun h => ?_)
  simp only [eligibleSomewhere, List.any_eq_true] at h
  obtain ⟨s, hs, hel⟩ := h
  have hw : s.val.kind.isWork = true := hsl.1 r d s.val i hel
  exact absurd ((hres s hs hw).symm.trans (hsl.2 r d s i hel)) (by simp)

/-- **§6.1's dayPlan_ok at ELEVEN of eleven, over the rows §8.3 is about, for EVERY
request.**

Five hypotheses, and **not one of them is about the log, the runtime or the shape of the day**:
`hagree` is the decoder's (gap 346), `hactive`, `hday` and `hnowcal` are R10 obligations, and
`hplain` is the same hypothesis `Planner.plan_never_moves_a_wall` has carried since P1.  W-19
left this day at nine of eleven with the two comparisons **refuted** at the permissive
eligibility; the sixth hypothesis is what repairs them, and it is a property of step 5's own
filter, not of any checker (`SlotAnchored`).

**`PlannerWit.dayPlan_ok_from_now_at_every_eligibility_is_refuted` still stands and is not
weakened by this.**  It computes both comparisons `false` at `PlannerWit.permissive` on this
very day at `PlannerWit.theQueuedRequest`, and `PlannerWit.the_whole_battery_passes_from_now_at_the_queued_request`
fires this theorem at the same request.  The pair is the statement: what separates a refuted
∀-`el` claim from a proved one is exactly one clause about where step 5 may assign. -/
theorem dayPlan_ok_from_now (el : Eligible) (r : PlanReq)
    (hagree : r.wallsAgree = true)
    (hactive : r.activeAgrees = true)
    (hday : r.dayAgrees = true)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd)
    (hplain : ∀ (i : Id) (e : Entity) (a b : Field.DT),
      r.plan.val.store.get i = some e → e.val.shape = Shape.interval a b →
      e.val.buffer = none ∧
        r.dayStart ≤ (Cal.instantOf r.tz a.day a.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec ≤ r.dayEnd ∧
        (Cal.instantOf r.tz a.day a.time).sec < (Cal.instantOf r.tz b.day b.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec < LogStamp.yearEnd)
    (hslot : SlotAnchored el) :
    planOk el r (withoutPast r (dayPlan r)) = true := by
  have hnone : ∀ i, eligibleSomewhere el r (withoutPast r (dayPlan r)) i = false :=
    eligibleSomewhere_of_only_the_reservation hslot r _
      (fun s hs hw => withoutPast_work_rows_are_the_reservation r s hs hw)
  exact dayPlan_ok_from_now_given_the_two_comparisons el r hagree hactive hday hnowcal hplain
    (monotoneInRank_of_nothing_eligible el r _ hnone)
    (hotBeforeQueue_of_nothing_eligible el r _ hnone)

/-- **The whole-day sibling: W-21's eleven with `hnorun` GONE.**  The class is *the log holds
no Block for today* — running or not — where `dayPlan_ok_on_a_quiet_day` additionally asks
that nothing be running.  The two are incomparable and both are kept (D5): this one drops a
hypothesis on the request and pays for it with `SlotAnchored` in place of `WorkAnchored`.

It is the weaker of this section's two lifts in one respect a reader should see: `hnopast` is
*"false of every real day after the first block is worked"* (`dayPlan_ok_core_from_now`'s own
doc comment), and `dayPlan_ok_from_now` above is the one with no such hypothesis at all. -/
theorem dayPlan_ok_on_a_day_with_no_replayed_block (el : Eligible) (r : PlanReq)
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
        (Cal.instantOf r.tz b.day b.time).sec < LogStamp.yearEnd)
    (hslot : SlotAnchored el) :
    planOk el r (dayPlan r) = true := by
  have hnone : ∀ i, eligibleSomewhere el r (dayPlan r) i = false :=
    eligibleSomewhere_of_only_the_reservation hslot r _
      (fun s hs hw => dayPlan_work_rows_are_the_reservation r hnopast s hs hw)
  have hcore := dayPlan_ok_core r hagree hactive hday hnowcal hnopast hplain
  simp only [planOk, checksOf, List.all_append, checksEligible, List.all_cons, List.all_nil,
    Bool.and_true, monotoneInRank_of_nothing_eligible el r _ hnone,
    hotBeforeQueue_of_nothing_eligible el r _ hnone,
    impossibleKept_is_true_because_its_subject_is_empty el r,
    batchDoesNotReachPast_is_true_because_its_subject_is_empty el r]
  exact hcore

/-! ### The census on that day: the ceiling is FOUR, and it is reached

Seven of the eleven have no subject on `withoutPast`'s day at a `SlotAnchored` eligibility —
the four `the_census_ceiling_is_seven` already names at every request, plus `overbook` and the
two comparisons.  `overbook` is the one that *changes sign* between the two days and the
reason is design §6.3 row 1 taken literally: its subject is a Block row that survives
`withoutActive`, every Block row of this day is the reservation, and `withoutActive` removes
exactly that.  A day where `overbook` has something to say is a day with a Block the fold
placed — which is P5's row, not in `Planner.dayRows` yet. -/

/-- A row filtered out of a list cannot give an `any` a witness the whole list did not. -/
theorem any_filter_of_any_eq_false {α : Type} {l : List α} {p q : α → Bool}
    (h : l.any q = false) : (l.filter p).any q = false := by
  refine Bool.eq_false_iff.2 (fun hx => ?_)
  obtain ⟨a, ha, hq⟩ := List.any_eq_true.1 hx
  exact absurd (List.any_eq_true.2 ⟨a, (List.mem_filter.1 ha).1, hq⟩) (by simp [h])

/-- **`overbook` has no subject on the rows §8.3 is about**, at every request: `withoutActive`
removes the only Block `withoutPast` leaves.  It DOES have one on the whole day — the replayed
past — which is why `the_census_ceiling_is_seven` counts it and this section does not. -/
theorem overbook_has_no_subject_from_now (el : Eligible) (r : PlanReq) :
    subjectOf el .overbook r (withoutPast r (dayPlan r)) = false := by
  simp only [subjectOf, withoutActive_segments]
  refine Bool.eq_false_iff.2 (fun h => ?_)
  obtain ⟨s, hs, hp⟩ := List.any_eq_true.1 h
  obtain ⟨hs', hna⟩ := List.mem_filter.1 hs
  simp only [beq_iff_eq] at hp
  have hact : isActive r s = true :=
    withoutPast_work_rows_are_the_reservation r s hs' (by rw [hp]; rfl)
  rw [hact] at hna
  simp at hna

theorem energyFilter_has_no_subject_from_now (el : Eligible) (r : PlanReq) :
    subjectOf el .energyFilter r (withoutPast r (dayPlan r)) = false := by
  simp only [subjectOf, withoutPast_segments]
  exact any_filter_of_any_eq_false (by
    have := energyFilter_has_no_subject el r
    simpa only [subjectOf] using this)

theorem windDown_has_no_subject_from_now (el : Eligible) (r : PlanReq)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd) :
    subjectOf el .windDown r (withoutPast r (dayPlan r)) = false := by
  simp only [subjectOf]
  refine Bool.eq_false_iff.2 (fun h => ?_)
  obtain ⟨b, hb, hp⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨hbk, -⟩, hany⟩ := hp
  obtain ⟨w, hw, hwp⟩ := List.any_eq_true.1 hany
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hwp
  have := no_block_row_of_the_day_reaches_the_wind_down r hnowcal b w
    (mem_withoutPast r _ b hb).1 (mem_withoutPast r _ w hw).1 hbk hwp.1
  omega

theorem batch_has_no_subject_from_now (el : Eligible) (r : PlanReq) :
    subjectOf el .batch r (withoutPast r (dayPlan r)) = false := by
  simp only [subjectOf]
  refine Bool.eq_false_iff.2 (fun h => ?_)
  obtain ⟨s, hs, hp⟩ := List.any_eq_true.1 h
  cases hk : s.val.kind
  case batch ids =>
    exact absurd hk (the_day_has_no_batch_row r s (mem_withoutPast r _ s hs).1 ids)
  all_goals (rw [hk] at hp; simp at hp)

theorem impossible_has_no_subject_from_now (el : Eligible) (r : PlanReq) :
    subjectOf el .impossible r (withoutPast r (dayPlan r)) = false := by
  simp only [subjectOf]
  show ((dayPlan r).diagnostics.impossible.val.any
    (fun p => eligibleSomewhere el r (withoutPast r (dayPlan r)) p.1)) = false
  simp only [the_day_names_no_impossible_item r, List.any_nil]

/-- The two comparisons' populations are empty whenever nothing is eligible anywhere. -/
theorem rankSubjects_of_nothing_eligible (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : ∀ i, eligibleSomewhere el r d i = false) : rankSubjects el r d = [] := by
  refine List.flatMap_eq_nil_iff.2 (fun i _ => List.filterMap_eq_nil_iff.2 (fun j _ => ?_))
  cases r.plan.val.store.get i <;> cases r.plan.val.store.get j <;> simp [h i]

theorem hotSubjects_of_nothing_eligible (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : ∀ i, eligibleSomewhere el r d i = false) : hotSubjects el r d = [] := by
  refine List.flatMap_eq_nil_iff.2 (fun i _ => List.filterMap_eq_nil_iff.2 (fun j _ => ?_))
  cases r.plan.val.store.get i <;> cases r.plan.val.store.get j <;> simp [h i]

theorem rank_has_no_subject_of_nothing_eligible (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : ∀ i, eligibleSomewhere el r d i = false) : subjectOf el .rank r d = false := by
  simp only [subjectOf, rankSubjects_of_nothing_eligible el r d h, List.isEmpty_nil,
    Bool.not_true]

theorem hot_has_no_subject_of_nothing_eligible (el : Eligible) (r : PlanReq) (d : DayPlan)
    (h : ∀ i, eligibleSomewhere el r d i = false) : subjectOf el .hot r d = false := by
  simp only [subjectOf, hotSubjects_of_nothing_eligible el r d h, List.isEmpty_nil,
    Bool.not_true]

/-- **FOUR is the ceiling of the census on the rows §8.3 is about, at every request and every
`SlotAnchored` eligibility** — `oneBlock`, `overWall`, `overBreak` and `wallMoved`, and the
other seven have nothing to range over.  `PlannerWit.the_eleven_from_now_is_four_checkers_biting`
reaches it, so four is a ceiling that has been touched and not a high-water mark.

**Read it beside `the_census_ceiling_is_seven`, not instead of it.**  That one is over the
WHOLE day at any eligibility and counts three checks this one does not — `overbook` and the
two comparisons — and all three are counted there because of the **replayed past**, the half
of the day §8.3's laws are not about.  Neither number corrects the other. -/
theorem the_census_ceiling_from_now_is_four {el : Eligible} (hsl : SlotAnchored el)
    (r : PlanReq) (hnowcal : r.now.sec + 1 < LogStamp.yearEnd) :
    subjectCount el r (withoutPast r (dayPlan r)) ≤ 4 := by
  have hnone : ∀ i, eligibleSomewhere el r (withoutPast r (dayPlan r)) i = false :=
    eligibleSomewhere_of_only_the_reservation hsl r _
      (fun s hs hw => withoutPast_work_rows_are_the_reservation r s hs hw)
  have e1 := overbook_has_no_subject_from_now el r
  have e2 := energyFilter_has_no_subject_from_now el r
  have e3 := windDown_has_no_subject_from_now el r hnowcal
  have e4 := rank_has_no_subject_of_nothing_eligible el r _ hnone
  have e5 := hot_has_no_subject_of_nothing_eligible el r _ hnone
  have e6 := impossible_has_no_subject_from_now el r
  have e7 := batch_has_no_subject_from_now el r
  show (List.filter (fun c => subjectOf el c.name r (withoutPast r (dayPlan r)))
    (checksOf el)).length ≤ 4
  have hcore : checksCore.filter
      (fun c => subjectOf el c.name r (withoutPast r (dayPlan r)))
      = ([⟨.oneBlock, oneBlockAtATime⟩, ⟨.overWall, noBlockOverAWall⟩,
          ⟨.overBreak, noBlockOverABreak⟩, ⟨.wallMoved, wallsUnmoved⟩] : List Check).filter
            (fun c => subjectOf el c.name r (withoutPast r (dayPlan r))) := by
    simp only [checksCore, List.filter_cons, e1, e2, e3, Bool.false_eq_true, if_false]
  have helig : (checksEligible el).filter
      (fun c => subjectOf el c.name r (withoutPast r (dayPlan r))) = [] := by
    simp only [checksEligible, List.filter_cons, e4, e5, e6, e7, Bool.false_eq_true, if_false,
      List.filter_nil]
  rw [checksOf, List.filter_append, List.length_append, hcore, helig]
  have b1 := List.length_filter_le
    (fun c => subjectOf el c.name r (withoutPast r (dayPlan r)))
    ([⟨.oneBlock, oneBlockAtATime⟩, ⟨.overWall, noBlockOverAWall⟩,
      ⟨.overBreak, noBlockOverABreak⟩, ⟨.wallMoved, wallsUnmoved⟩] : List Check)
  simp only [List.length_cons, List.length_nil] at b1
  omega


/-! ############################################################################
## W-23: the eligibility axis closes on the WHOLE day, and what is left is the log
############################################################################

W-22 put §6.1's `planOk` at eleven of eleven over `withoutPast`'s day for **every** request,
and left the whole day standing on a hypothesis about the log: `dayPlan_ok_on_a_day_with_no_
replayed_block` needs `hnopast`, which its own doc comment calls *"false of every real day
after the first block is worked"*.  This section asks what the whole day is worth at every
request, and the answer is two halves that have to be read together.

**The positive half.**  `SlotAnchored` plus one clause — *the row has not already started* —
makes all four eligibility-dependent conjuncts vacuous on the **whole** day, at every request,
with nothing whatever assumed about the log.  `dayPlan_ok_is_the_core_seven` is the statement,
and it is a `Bool` **equality** rather than an implication: at such an eligibility
`planOk el r (dayPlan r)` *is* `planOkCore r (dayPlan r)`.  So the whole of §6.1's lift on the
whole day is the seven eligibility-free checks and nothing else — the eligibility axis
contributes nothing more, at any request, and closes.

**Why that clause is step 5's own and not a patch fitted to a witness.**  §8.2 step 3 cuts the
day's free slots from `now` forward — `Planner.PlanReq.cutFrom` is `now` clamped into the
window, and it is the cut's own left end — so a row that started before `now` is not a slot
step 5 can assign into — the same argument `SlotAnchored` makes one row over about
choice 5b's reservation, which choice 5b takes out of the slot supply.  `keepFromNow` is
W-17's own reader of *"has this row already started"* and it is reused rather than re-spelled
(AGENTS §5.3), so `FromNowAnchored` introduces no third reading of anything.  What P5 owes
the lift beside Planner.eligibleAt is now **three** lines, not two (README gaps 1061, 1170,
and **1281**).

**The negative half, which is why the positive half needs the clause at all.**  Drop it and
the whole-day lift is **false**.  `PlannerWit.dayPlan_ok_on_the_whole_day_at_a_slot_anchored_
eligibility_is_refuted` computes `planOk` `false` at `PlannerWit.theIdleQueuedRequest` — every
one of `dayPlan_ok_from_now`'s five hypotheses satisfied, at `PlannerWit.onlyOnFreeWorkRows`,
which **is** `SlotAnchored` — with no mutation of the day at all.  The two conjuncts that fail
are W-19's two comparisons and the cause is one row: a block the log replayed onto the morning
for the sibling that ranks *second*, while the hot sibling that ranks first reaches no row of
the day.  That row is not a row §8.3's laws are about, which is the whole reason `withoutPast`
exists — and it is a **work** row, so `SlotAnchored` alone cannot see past it.

**What that buys, exactly, is one of `hnopast`'s two uses.**  `dayPlan_ok_on_a_day_with_no_
replayed_block` spends it **twice**: once on the seven core checks (through `dayPlan_ok_core`)
and once on the four comparisons (through `dayPlan_work_rows_are_the_reservation`).  This
section removes the **second** use outright — the comparisons need no hypothesis about the log
at all, only a third clause on the eligibility — and leaves the first exactly where it was.
`PlannerWit.the_core_seven_is_false_on_three_whole_days` is why the first cannot simply be
dropped after it: `planOkCore` is `false` on the whole day at three requests this kernel
already builds, each one a recorded refutation of a goal that quantified over the replayed
past.  **So how far §6.1's lift goes is now a bounded statement on both axes**, and what
stands between it and the whole day is the **log**, one named checker at a time, and no part
of it is the assign fold's.

**What the closure is worth, and the number is FIVE.**  The four eligibility-dependent
conjuncts are vacuous under `FromNowAnchored`, so the census falls from the whole-day ceiling
of seven to `the_census_ceiling_on_the_whole_day_is_five`, reached at
`PlannerWit.theCensusRequest` (`PlannerWit.the_whole_day_census_at_the_from_now_eligibility_is_
five`).  **That is the cost of the clause, said in the same breath as the benefit**: the two
checks it buys a proof for are the two it takes the subject away from, and a reader who wants
the one number that does not move should read the SUBJECT row of W-22's table above — seven,
whole day, every request, every eligibility. -/

/-- **An eligibility that admits a candidate only where §8.2 step 5 could put one, on the
whole day**: `SlotAnchored` (W-22) plus the clause step 3's cut makes true — the day's free
slots begin at `Planner.PlanReq.cutFrom`, which is `now` clamped into the window, so a row
that has already started is not one of them.

`keepFromNow` is reused rather than re-spelled (AGENTS §5.3): it is W-17's own reader of the
same instant, the one `withoutPast` filters with, so the two cannot drift apart.  This is the
third of the three lines P5 owes the lift beside Planner.eligibleAt, and
`PlannerWit.fromNowWorkRows` is the concrete instance that fires it today. -/
def FromNowAnchored (el : Eligible) : Prop :=
  SlotAnchored el ∧
    ∀ (r : PlanReq) (d : DayPlan) (s : WfSeg) (i : Id),
      el r d s.val i = true → keepFromNow r s = true

/-- **A `FromNowAnchored` eligibility admits nothing at all on the WHOLE day, at every
request.**  The row it is offered is a work row (clause 1) that has not started (clause 3), so
it is a work row of `withoutPast`'s day, so it is choice 5b's reservation
(`withoutPast_work_rows_are_the_reservation`) — and clause 2 says it is not.

This is `eligibleSomewhere_of_only_the_reservation` moved off the smaller day: there the
filter was applied to the day and the hypothesis was about the rows that survived; here the
filter is applied to the eligibility and the day is left whole. -/
theorem eligibleSomewhere_of_nothing_from_now {el : Eligible} (hfn : FromNowAnchored el)
    (r : PlanReq) (i : Id) : eligibleSomewhere el r (dayPlan r) i = false := by
  refine Bool.eq_false_iff.2 (fun h => ?_)
  simp only [eligibleSomewhere, List.any_eq_true] at h
  obtain ⟨s, hs, hel⟩ := h
  have hw : s.val.kind.isWork = true := hfn.1.1 r (dayPlan r) s.val i hel
  have hmem : s ∈ (withoutPast r (dayPlan r)).segments := by
    rw [withoutPast_segments]
    exact List.mem_filter.2 ⟨hs, hfn.2 r (dayPlan r) s i hel⟩
  exact absurd ((withoutPast_work_rows_are_the_reservation r s hmem hw).symm.trans
    (hfn.1.2 r (dayPlan r) s i hel)) (by simp)

/-- **§6.1's eleven on the whole day IS §6.1's seven, at every request and every
`FromNowAnchored` eligibility.**  An equality, not an implication: nothing is assumed about
the log, the runtime or the day, and the four eligibility-dependent conjuncts are `true` on
both sides of it.

**Read it as a closure, not as an advance in coverage.**  What it says is that the eligibility
axis of §6.1's lift has nothing left to give on the whole day — every remaining conjunct of
the battery is one of the seven, and each of those is refuted or proved on its own merits by a
statement about the replayed past.  `the_census_ceiling_on_the_whole_day_is_five` is the price
paid for it, in subjects. -/
theorem dayPlan_ok_is_the_core_seven {el : Eligible} (hfn : FromNowAnchored el) (r : PlanReq) :
    planOk el r (dayPlan r) = planOkCore r (dayPlan r) := by
  have hnone : ∀ i, eligibleSomewhere el r (dayPlan r) i = false :=
    eligibleSomewhere_of_nothing_from_now hfn r
  simp only [planOk, planOkCore, checksOf, List.all_append, checksEligible, List.all_cons,
    List.all_nil, Bool.and_true,
    monotoneInRank_of_nothing_eligible el r _ hnone,
    hotBeforeQueue_of_nothing_eligible el r _ hnone,
    impossibleKept_is_true_because_its_subject_is_empty el r,
    batchDoesNotReachPast_is_true_because_its_subject_is_empty el r]

/-- The same, as the discharge a later step will want: the whole battery on the whole day
follows from the seven alone.  `PlannerWit.the_from_now_lift_holds_where_the_slot_anchored_
one_is_refuted` fires it, at the one request where the lift at a merely `SlotAnchored`
eligibility is refuted; `PlannerWit.the_core_seven_is_false_on_three_whole_days` is why it is
not a theorem about every request. -/
theorem dayPlan_ok_of_the_core_seven {el : Eligible} (hfn : FromNowAnchored el) (r : PlanReq)
    (hcore : planOkCore r (dayPlan r) = true) : planOk el r (dayPlan r) = true :=
  (dayPlan_ok_is_the_core_seven hfn r).trans hcore

/-- **FIVE is the ceiling of the census on the whole day at a `FromNowAnchored` eligibility**,
for every request — `the_census_ceiling_is_seven`'s five survivors minus the two comparisons,
which lose their subject with their quantifier.  `PlannerWit.the_whole_day_census_at_the_from_
now_eligibility_is_five` reaches it at the census request, so five is touched and not a
high-water mark.

**Read it beside seven, not instead of it.**  Seven is the ceiling on the same day at *any*
eligibility and it is the repo's headline (W-22's table above); five is what one hypothesis on
the eligibility costs in subjects, and the two checks it removes are exactly the two
`dayPlan_ok_is_the_core_seven` buys a proof for.  Neither number corrects the other. -/
theorem the_census_ceiling_on_the_whole_day_is_five {el : Eligible} (hfn : FromNowAnchored el)
    (r : PlanReq) (hnowcal : r.now.sec + 1 < LogStamp.yearEnd) :
    subjectCount el r (dayPlan r) ≤ 5 := by
  have hnone : ∀ i, eligibleSomewhere el r (dayPlan r) i = false :=
    eligibleSomewhere_of_nothing_from_now hfn r
  have e1 := energyFilter_has_no_subject el r
  have e2 := windDown_has_no_subject el r hnowcal
  have e3 := rank_has_no_subject_of_nothing_eligible el r _ hnone
  have e4 := hot_has_no_subject_of_nothing_eligible el r _ hnone
  have e5 := impossible_has_no_subject el r
  have e6 := batch_has_no_subject el r
  show (List.filter (fun c => subjectOf el c.name r (dayPlan r)) (checksOf el)).length ≤ 5
  have hcore : checksCore.filter (fun c => subjectOf el c.name r (dayPlan r))
      = ([⟨.overbook, noOverbook⟩, ⟨.oneBlock, oneBlockAtATime⟩,
          ⟨.overWall, noBlockOverAWall⟩, ⟨.overBreak, noBlockOverABreak⟩,
          ⟨.wallMoved, wallsUnmoved⟩] : List Check).filter
            (fun c => subjectOf el c.name r (dayPlan r)) := by
    simp only [checksCore, List.filter_cons, e1, e2, Bool.false_eq_true, if_false]
  have helig : (checksEligible el).filter (fun c => subjectOf el c.name r (dayPlan r)) = [] := by
    simp only [checksEligible, List.filter_cons, e3, e4, e5, e6, Bool.false_eq_true, if_false,
      List.filter_nil]
  rw [checksOf, List.filter_append, List.length_append, hcore, helig]
  have b1 := List.length_filter_le (fun c => subjectOf el c.name r (dayPlan r))
    ([⟨.overbook, noOverbook⟩, ⟨.oneBlock, oneBlockAtATime⟩,
      ⟨.overWall, noBlockOverAWall⟩, ⟨.overBreak, noBlockOverABreak⟩,
      ⟨.wallMoved, wallsUnmoved⟩] : List Check)
  simp only [List.length_cons, List.length_nil] at b1
  omega


/-! ############################################################################
## W-24: the LOG axis, one named clause at a time — and THREE of the seven owe it nothing
############################################################################

W-23 closed the **eligibility** axis on the whole day: `dayPlan_ok_is_the_core_seven` says
§6.1's eleven *is* §6.1's seven there, at every request, so what stands between the lift and
the whole day is the **replayed past** and nothing else.  Its own closing sentence named the
work — *"the log, one named checker at a time"* — and this section is that.

**`hnopast` is one hypothesis doing four jobs, and it is false of every real day.**
`dayPlan_ok_core` carries *"the log holds no Block for today"* and spends it on the six
block-side checks at once, by emptying their subject.  `dayPlan_ok_core`'s own doc comment
calls that *"false of every real day after the first block is worked"*, and
`PlannerWit.the_log_at_the_census_request_holds_a_block` computes a request where it is: the
§4.3 Wednesday, whose log replays **two** Block rows and a break.

**Three of the seven owe the log nothing at all, and that is the first half of the answer.**
`energyFilterOk` and `noDemandingAfterWindDown` are vacuous at **every** request
(`energyFilter_has_no_subject`, `windDown_has_no_subject`), and `wallsUnmoved` never reads a
Block row — its subject is the Wall rows the plan's own index puts there, which is why
`dayPlan_ok_core`'s `h7` never touches `hnopast`.  So the whole of the log's debt to §6.1's
seven is **four** clauses, and `PastPays` is them.

**Each clause is about the LOG, not about the day**, except the one that is a sum.  Three are
`∀ t ∈ Planner.pastRows r` — the rows as the replay wrote them, before `Planner.segOf` and
before the sort — because that is the form a caller can discharge by reading the log.  The
fourth is `blockSeconds` over `pastHalf`, the day's own meter applied to the day's own
replayed half: re-summing the log beside it would be a second reader of the same number,
which is the defect this kernel is named after (AGENTS §5.3).  `pastHalf` is `withoutPast`'s
complement and uses `keepFromNow` — the same one instant, not a second reading of it.

**The bound in the other direction is four refuted days, three of them already here.**
`PlannerWit.the_core_seven_is_false_on_three_whole_days` computes `planOkCore = false` at
`theMorningWallRequest`, `theShortBlockRequest` and `theMidBreakRequest`, and
`PlannerWit.the_paying_past_fails_on_four_whole_days` computes which clause of `PastPays`
fails at each, and adds a fourth day for the fourth clause.  Every row of it has exactly one
`false`, so no clause of the four is implied by the other three and none is a checker nothing
can fail (AGENTS §9.2's *"a check no input can fail"*).  The fourth day is
`PlannerWit.theOverBudgetRequest`, **built for the `budget` clause** because nothing in the
witness set reached it — AGENTS §9.2 again, and D40's own rule that a mutation nothing fails
is fixed by building the witness rather than recorded.

**What this is not.**  It is not a step towards §6.2's fold induction and it does not touch
it: every theorem here holds *because* §8.2 step 5's Block and Batch rows are absent from the
day (`Planner.dayRows`' own doc comment), which is the same sentence as `hblk`'s with the
opposite sign.  And it moves no census number: `PastPays` is a hypothesis, not a checker, and
`subjectOf` does not read it. -/

/-- **The day's replayed half** — the rows `withoutPast` drops, and nothing else touched.

This is `withoutPast`'s complement over the **same** `keepFromNow`, so the two cannot drift
apart and no second reading of *"has this row already started"* enters the module
(AGENTS §5.3).  It exists so that the one clause of `PastPays` that is a **sum** can be
weighed with `Planner.blockSeconds`, the day's own meter, rather than with a second one
written over the log. -/
def pastHalf (r : PlanReq) (d : DayPlan) : DayPlan :=
  { d with segments := d.segments.filter (fun s => !keepFromNow r s) }

theorem pastHalf_segments (r : PlanReq) (d : DayPlan) :
    (pastHalf r d).segments = d.segments.filter (fun s => !keepFromNow r s) := rfl

/-- **Under the lift's own R10 hypothesis the forcing is the identity on every replayed row.**
`Planner.pastRows` ends each row it produces at `now` and starts it at or after `day_start`,
and `hnowcal` puts `now` inside the calendar, so `Planner.segOf`'s clamp has nothing to do.
This is what lets a clause written over the log be read off the row the day actually holds. -/
theorem segOf_replayed (r : PlanReq) (hnowcal : r.now.sec + 1 < LogStamp.yearEnd)
    (t : Seg) (ht : t ∈ pastRows r) : (segOf t).val = t := by
  obtain ⟨-, hlt, hstop⟩ := pastRows_end_at_now r t ht
  refine segOf_is_the_row_inside_the_calendar t (Nat.le_of_lt hlt) ?_
  simp only [LogStamp.yearEnd] at *
  omega

/-- **A Block row that is not §8.2 choice 5b's reservation has already started**, at every
request and with nothing assumed about the log — `a_block_row_from_now_is_the_reservation`
read the other way round.  It is what makes `withoutActive`'s Block rows a sub-filter of
`pastHalf`'s, which is the whole of the `overbook` clause's reduction. -/
theorem a_block_row_that_is_not_the_reservation_has_started (r : PlanReq) (s : WfSeg)
    (hs : s ∈ (dayPlan r).segments) (hk : s.val.kind = SegKind.block)
    (hna : isActive r s = false) : keepFromNow r s = false := by
  cases hkeep : keepFromNow r s with
  | false => rfl
  | true =>
    have hmem : s ∈ (withoutPast r (dayPlan r)).segments := by
      rw [withoutPast_segments]; exact List.mem_filter.2 ⟨hs, hkeep⟩
    have hw : s.val.kind.isWork = true := by rw [hk]; rfl
    exact absurd ((withoutPast_work_rows_are_the_reservation r s hmem hw).symm.trans hna)
      (by simp)

/-- **A sum over a filtered list only grows when the filter admits more.**  `Planner.block
Seconds` is a `foldl` of `+` over one filter of the day's rows, so this is the whole of what a
comparison between two of its filters needs — no permutation, no sort, and no second walk. -/
theorem foldl_add_filter_le {α : Type} (g : α → Nat) (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) →
      ∀ a b : Nat, a ≤ b →
        (l.filter p).foldl (fun n x => n + g x) a ≤ (l.filter q).foldl (fun n x => n + g x) b := by
  intro l
  induction l with
  | nil => intro _ a b hab; simpa using hab
  | cons x l ih =>
    intro h a b hab
    have htail : ∀ y ∈ l, p y = true → q y = true := fun y hy => h y (List.mem_cons_of_mem _ hy)
    cases hp : p x with
    | true =>
      have hq : q x = true := h x (by simp) hp
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq]
      simpa using ih htail (a + g x) (b + g x) (by omega)
    | false =>
      rw [List.filter_cons_of_neg (by simp [hp])]
      cases hq : q x with
      | true =>
        rw [List.filter_cons_of_pos hq]
        simpa using ih htail a (b + g x) (by omega)
      | false =>
        rw [List.filter_cons_of_neg (by simp [hq])]
        exact ih htail a b hab

/-- **The Blocks `overbook` weighs are a sub-filter of the ones the log replayed**, at every
request.  `withoutActive` removes the reservation, and every other Block row of the day has
already started (`a_block_row_that_is_not_the_reservation_has_started`), so `pastHalf` holds
all of them — and possibly more, because a replayed Block of the *running* item is dropped by
`withoutActive` and kept by `pastHalf`. -/
theorem blockSeconds_withoutActive_le_pastHalf (r : PlanReq) :
    blockSeconds (withoutActive r (dayPlan r)) ≤ blockSeconds (pastHalf r (dayPlan r)) := by
  have hstep : ∀ x ∈ (dayPlan r).segments,
      (decide (x.val.kind = SegKind.block) && (!isActive r x)) = true →
        (decide (x.val.kind = SegKind.block) && (!keepFromNow r x)) = true := by
    intro x hx hxx
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hxx ⊢
    exact ⟨hxx.1, by rw [a_block_row_that_is_not_the_reservation_has_started r x hx hxx.1 hxx.2]⟩
  have e1 : blockSeconds (withoutActive r (dayPlan r))
      = ((dayPlan r).segments.filter
          (fun s => decide (s.val.kind = SegKind.block) && (!isActive r s))).foldl
            (fun a s => a + (s.val.stop - s.val.start)) 0 := by
    unfold blockSeconds
    rw [withoutActive_segments, List.filter_filter]
  have e2 : blockSeconds (pastHalf r (dayPlan r))
      = ((dayPlan r).segments.filter
          (fun s => decide (s.val.kind = SegKind.block) && (!keepFromNow r s))).foldl
            (fun a s => a + (s.val.stop - s.val.start)) 0 := by
    unfold blockSeconds
    rw [pastHalf_segments, List.filter_filter]
  rw [e1, e2]
  exact foldl_add_filter_le (fun s : WfSeg => s.val.stop - s.val.start) _ _
    (dayPlan r).segments hstep 0 0 (Nat.le_refl 0)

/-- **What the replayed past owes §6.1's seven, clause by clause.**

`dayPlan_ok_core`'s `hnopast` — *the log holds no Block for today* — discharges all four at
once, by emptying their subject, and is false of every day whose morning worked something
(`PastPays_of_no_past_block` is that implication, and
`PlannerWit.the_paying_past_holds_where_hnopast_does_not` is a request where the weaker one
holds and the stronger does not).

Three clauses are about the rows the replay wrote; the fourth is the day's own `Planner.
blockSeconds` over `pastHalf`, for the reason the section header gives.  `energyFilterOk`,
`noDemandingAfterWindDown` and `wallsUnmoved` are absent because they owe the log nothing. -/
structure PastPays (r : PlanReq) : Prop where
  /-- `oneBlock`: no Block the log replays runs longer than one block. -/
  oneBlock : ∀ t ∈ pastRows r, t.kind = SegKind.block → t.stop - t.start ≤ r.blockMin * 60
  /-- `overWall`: no Block the log replays overlaps a span the day's walls blocked out.
  `Planner.blockedByWalls` is the index `Planner.a_wall_row_sits_in_a_blocked_span` places
  every Wall row inside, so this clause is about the plan's calendar and the log, and about
  no row of the produced day. -/
  offWall : ∀ t ∈ pastRows r, t.kind = SegKind.block →
    ∀ v ∈ blockedByWalls r, t.stop ≤ v.1 ∨ v.2 ≤ t.start
  /-- `overBreak`: no Block the log replays covers a break the log replays.  Both sides are
  the log's (`Planner.a_break_row_is_a_replayed_row`), which is why the clause needs no third
  quantifier over the day. -/
  offBreak : ∀ t ∈ pastRows r, ∀ u ∈ pastRows r,
    t.kind = SegKind.block → u.kind = SegKind.brk → t.stop ≤ u.start ∨ u.stop ≤ t.start
  /-- `overbook`: the Blocks already worked fit the day's budget. -/
  budget : blockSeconds (pastHalf r (dayPlan r)) ≤
    (dayPlan r).budgetBlocks * (dayPlan r).blockMin * 60

/-- **`hnopast` pays all four**, which is what makes the lift below strictly more general than
`dayPlan_ok_core` rather than a second incomparable one: a day whose log holds no Block
satisfies `PastPays` with three clauses vacuous and the fourth `0 ≤ _`. -/
theorem PastPays_of_no_past_block (r : PlanReq)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd)
    (hnopast : ∀ t ∈ pastRows r, t.kind ≠ SegKind.block) : PastPays r where
  oneBlock t ht hk := absurd hk (hnopast t ht)
  offWall t ht hk := absurd hk (hnopast t ht)
  offBreak t ht _ _ hk _ := absurd hk (hnopast t ht)
  budget := by
    have hnb : (pastHalf r (dayPlan r)).segments.any
        (fun s => s.val.kind == SegKind.block) = false := by
      refine Bool.eq_false_iff.2 (fun h => ?_)
      simp only [List.any_eq_true, beq_iff_eq] at h
      obtain ⟨s, hs, hk⟩ := h
      rw [pastHalf_segments] at hs
      obtain ⟨hs', hkeep⟩ := List.mem_filter.1 hs
      obtain ⟨t, ht, rfl⟩ := dayPlan_block_rows_are_the_reservation r hnopast s hs' hk
      obtain ⟨q, hq, -, -, -, -, -, -⟩ := r.mem_activeRow t ht
      obtain ⟨e1, -, -, -⟩ := the_reservation_row_is_exact r q hq hnowcal t ht
      have hkf : keepFromNow r (segOf t) = true := by
        unfold keepFromNow; rw [e1]; simp
      rw [hkf] at hkeep
      simp at hkeep
    rw [blockSeconds_of_no_block _ hnb]
    exact Nat.zero_le _


/-! ### The third axis: what the WALL law needs, and what the lift was asking for

W-23 named the eligibility bound (`FromNowAnchored`) and W-24 named the log bound
(`PastPays`).  The lift's remaining unnamed hypothesis is the one below, and it had the shape
the other two had before somebody looked: a blanket `∀` over the request, discharged in this
tree only by a `decide` at a witness, and **false of an ordinary week file**.

`PlainStore` is that blanket, named so it can be refuted rather than only assumed.  It ranges
over **every** entity of the plan, so a plan holding one `at:` event on **another day** fails
it — and a week file with an event on another day is the ordinary case, not an edge one.
`PlannerWit.theOffDayRequest` is a request where it is false and §6.1's seven hold anyway.

`WallsArePlain` is what the seven actually need, read off the one consumer:
`dayPlan_ok_core_of_plain_walls`'s `h7` applies the blanket under `hs`, `hk` and `hi`, so the
entities it reaches are exactly the ones a **Wall row of the produced day** names.  No other
checker of the seven mentions `buffer:` or the day's two ends. -/

/-- **The lift's blanket plainness hypothesis, named.**  Every interval-shaped entity of the
plan carries no `buffer:`, lies inside the day being planned, runs forwards, and ends inside
the calendar.  Quantified over the **store**, so one `at:` event on another day refutes it
(`PlannerWit.the_blanket_plainness_is_false_at_the_off_day_request`). -/
def PlainStore (r : PlanReq) : Prop :=
  ∀ (i : Id) (e : Entity) (a b : Field.DT),
    r.plan.val.store.get i = some e → e.val.shape = Shape.interval a b →
    e.val.buffer = none ∧
      r.dayStart ≤ (Cal.instantOf r.tz a.day a.time).sec ∧
      (Cal.instantOf r.tz b.day b.time).sec ≤ r.dayEnd ∧
      (Cal.instantOf r.tz a.day a.time).sec < (Cal.instantOf r.tz b.day b.time).sec ∧
      (Cal.instantOf r.tz b.day b.time).sec < LogStamp.yearEnd

/-- **The same five clauses, restricted to the entities a Wall row of `d` names.**  This is
what `wallsUnmoved` reads and it is all of it: `Planner.plan_never_moves_a_wall` is fired once
per Wall row, on the item that row carries.  An entity the day never places a Wall for is not
this law's business, and `PlainStore` was asking about it anyway. -/
def WallsArePlain (r : PlanReq) (d : DayPlan) : Prop :=
  ∀ s ∈ d.segments, s.val.kind = SegKind.wall →
    ∀ (i : Id) (e : Entity) (a b : Field.DT),
      s.val.item = some i → r.plan.val.store.get i = some e →
      e.val.shape = Shape.interval a b →
      e.val.buffer = none ∧
        r.dayStart ≤ (Cal.instantOf r.tz a.day a.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec ≤ r.dayEnd ∧
        (Cal.instantOf r.tz a.day a.time).sec < (Cal.instantOf r.tz b.day b.time).sec ∧
        (Cal.instantOf r.tz b.day b.time).sec < LogStamp.yearEnd

/-- **The blanket pays the restriction**, on every day — which is what makes the lift below
strictly more general than the one it replaces rather than a second incomparable one, exactly
as `PastPays_of_no_past_block` does for the log axis. -/
theorem WallsArePlain_of_a_plain_store (r : PlanReq) (d : DayPlan) (h : PlainStore r) :
    WallsArePlain r d := fun _ _ _ i e a b _ hget hsh => h i e a b hget hsh


/-- **§6.1's seven on the WHOLE day, from a paying past and from plain WALLS.**

Same seven checkers, same conjunction, same request-side hypotheses as `dayPlan_ok_core` —
and in place of *"the log holds no Block for today"*, the four clauses of `PastPays`, each a
statement about the rows the replay wrote rather than an assumption that there are none.

**Three of the seven take no clause at all.**  `energyFilterOk` and
`noDemandingAfterWindDown` are discharged by `energyFilterOk_is_true_because_its_subject_is
_empty` and `noDemandingAfterWindDown_is_true_because_its_subject_is_empty`, which hold at
every request; `wallsUnmoved` is P1's `Planner.plan_never_moves_a_wall` over the Wall rows and
never reads a Block.  That is why `PastPays` has four fields and not six.

**What it is worth, and what it is not.**  `PastPays_of_no_past_block` makes `dayPlan_ok_core`
a corollary of this, and `PlannerWit.the_paying_past_holds_where_hnopast_does_not` exhibits a
request where this fires and that one cannot — so the whole-day lift now reaches days whose
morning worked something, which is every real day.  It is **not** a step towards §6.2's fold
induction: every clause below is discharged by a row that is either replayed or is §8.2
choice 5b's reservation, and §8.2 step 5's own Block rows are still absent from
`Planner.dayRows`. -/
theorem dayPlan_ok_core_of_plain_walls (r : PlanReq)
    (hagree : r.wallsAgree = true)
    (hactive : r.activeAgrees = true)
    (hday : r.dayAgrees = true)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd)
    (hwalls : WallsArePlain r (dayPlan r))
    (hpast : PastPays r) :
    planOkCore r (dayPlan r) = true := by
  -- **Every Block row of the day is a replayed row or the reservation**, unconditionally —
  -- `dayPlan_ok_core`'s `hblk` with the case `hnopast` used to close left open.
  have hres : ∀ s ∈ (dayPlan r).segments, s.val.kind = SegKind.block →
      (∃ t ∈ pastRows r, s.val = t) ∨
      (∃ q, r.activeRun = some q ∧ s.val.start = r.now.sec ∧ r.now.sec < s.val.stop ∧
        s.val.stop ≤ q.stop ∧ s.val.stop < LogStamp.yearEnd) := by
    intro s hs hk
    rcases dayPlan_block_rows_are_replayed_or_reserved r s hs hk with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · exact Or.inl ⟨t, ht, segOf_replayed r hnowcal t ht⟩
    · obtain ⟨q, hq, -, -, -, -, -, -⟩ := r.mem_activeRow t ht
      obtain ⟨e1, e2, e3, e4⟩ := the_reservation_row_is_exact r q hq hnowcal t ht
      exact Or.inr ⟨q, hq, e1, e2, e3, e4⟩
  have h1 : noOverbook r (dayPlan r) = true :=
    (noOverbook_iff r _).mpr
      (Nat.le_trans (blockSeconds_withoutActive_le_pastHalf r) hpast.budget)
  have h2 : oneBlockAtATime r (dayPlan r) = true := by
    refine (oneBlockAtATime_iff r _).mpr (fun s hs hk => ?_)
    have hbm : (dayPlan r).blockMin = r.blockMin := rfl
    rcases hres s hs hk with ⟨t, ht, hst⟩ | ⟨q, hq, e1, e2, e3, -⟩
    · have hkt : t.kind = SegKind.block := by rw [← hst]; exact hk
      have := hpast.oneBlock t ht hkt
      rw [hbm, hst]
      exact this
    · have hone := r.the_reservation_is_at_most_one_block q hactive (r.blockMin_pos hday) hq
      obtain ⟨-, -, -, -, hs0, -⟩ := r.activeRun_spec q hq
      rw [hbm]
      omega
  have h3 : energyFilterOk r (dayPlan r) = true :=
    energyFilterOk_is_true_because_its_subject_is_empty r
  have h4 : noBlockOverAWall r (dayPlan r) = true := by
    refine (noBlockOverAWall_iff r _).mpr (fun b hb w hw hbk hwk => ?_)
    obtain ⟨v, hv, hvlt, hv1, hv2⟩ :=
      a_wall_row_sits_in_a_blocked_span r w (dayPlan_segments r ▸ hw) hwk
    rcases hres b hb hbk with ⟨t, ht, hst⟩ | ⟨q, hq, e1, e2, e3, e4⟩
    · have hkt : t.kind = SegKind.block := by rw [← hst]; exact hbk
      obtain ⟨-, -, hstop⟩ := pastRows_end_at_now r t ht
      have hd := hpast.offWall t ht hkt v hv
      rw [hst]
      simp only [clampSec, LogStamp.yearEnd] at hv1 hnowcal
      omega
    · obtain ⟨-, -, -, -, hs0, hlt, -⟩ := r.activeRun_spec q hq
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
    obtain ⟨u, hu, rfl⟩ := a_break_row_is_a_replayed_row r k (dayPlan_segments r ▸ hk) hkk
    have hsu : (segOf u).val = u := segOf_replayed r hnowcal u hu
    have hku : u.kind = SegKind.brk := by rw [← hsu]; exact hkk
    obtain ⟨-, -, hustop⟩ := pastRows_end_at_now r u hu
    rcases hres b hb hbk with ⟨t, ht, hst⟩ | ⟨q, hq, e1, -, -, -⟩
    · have hkt : t.kind = SegKind.block := by rw [← hst]; exact hbk
      have hd := hpast.offBreak t ht u hu hkt hku
      rw [hst, hsu]
      exact hd
    · right
      rw [hsu, e1]
      exact hustop
  have h6 : noDemandingAfterWindDown r (dayPlan r) = true :=
    noDemandingAfterWindDown_is_true_because_its_subject_is_empty r hnowcal
  have h7 : wallsUnmoved r (dayPlan r) = true := by
    refine (wallsUnmoved_iff r _).mpr (fun s hs i e a b hi hget hsh hk => ?_)
    obtain ⟨hnbuf, hin, hout, hfwd, hcal⟩ := hwalls s hs hk i e a b hi hget hsh
    exact plan_never_moves_a_wall r s i e a b hagree hs hk hi hget hsh hnbuf hin hout hfwd hcal
  simp only [planOkCore, checksCore, List.all_cons, List.all_nil, Bool.and_true,
    h1, h2, h3, h4, h5, h6, h7]

/-- **The blanket form, now a corollary.**  The statement is unchanged from before the wall
axis was named and its proof is one application of `WallsArePlain_of_a_plain_store`, so every
caller holding the store-wide hypothesis keeps working and none has to produce the restricted
one.

**`PlannerWit.the_off_day_request_has_plain_walls` is the other half of the strictness claim**:
a request where `PlainStore` is false, `WallsArePlain` holds, and the seven hold with it. -/
theorem dayPlan_ok_core_of_a_paying_past (r : PlanReq)
    (hagree : r.wallsAgree = true)
    (hactive : r.activeAgrees = true)
    (hday : r.dayAgrees = true)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd)
    (hplain : PlainStore r)
    (hpast : PastPays r) :
    planOkCore r (dayPlan r) = true :=
  dayPlan_ok_core_of_plain_walls r hagree hactive hday hnowcal
    (WallsArePlain_of_a_plain_store r _ hplain) hpast


/-- **The whole battery on the whole day, from a paying past** — `dayPlan_ok_is_the_core_seven`
composed with the theorem above, which is the form a later step will call: §6.1's eleven, on
the whole day, at every `FromNowAnchored` eligibility, for every request whose log pays.

Both bounds W-23 left are now named rather than assumed: the eligibility one by
`FromNowAnchored`, the log one by `PastPays`. -/
theorem dayPlan_ok_on_the_whole_day {el : Eligible} (hfn : FromNowAnchored el) (r : PlanReq)
    (hagree : r.wallsAgree = true) (hactive : r.activeAgrees = true) (hday : r.dayAgrees = true)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd)
    (hplain : PlainStore r)
    (hpast : PastPays r) : planOk el r (dayPlan r) = true :=
  dayPlan_ok_of_the_core_seven hfn r
    (dayPlan_ok_core_of_a_paying_past r hagree hactive hday hnowcal hplain hpast)


/-- **The whole battery on the whole day, from a paying past and plain walls** — the strongest
form of §6.1's lift in this tree, and the one a later step should call.

Three bounds, three names: the eligibility one by `FromNowAnchored` (W-23), the log one by
`PastPays` (W-24), the wall one by `WallsArePlain` (here).  Nothing else in the hypotheses is
a `∀` over the request: `wallsAgree`, `activeAgrees` and `dayAgrees` are decidable `Bool`s the
decoder owes (gap 346) and `hnowcal` is one `Nat` comparison.

`dayPlan_ok_on_the_whole_day` is the same statement with the blanket `PlainStore` in place of
`WallsArePlain`, kept because every existing caller has the blanket. -/
theorem dayPlan_ok_on_the_whole_day_of_plain_walls {el : Eligible} (hfn : FromNowAnchored el)
    (r : PlanReq)
    (hagree : r.wallsAgree = true) (hactive : r.activeAgrees = true) (hday : r.dayAgrees = true)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd)
    (hwalls : WallsArePlain r (dayPlan r))
    (hpast : PastPays r) : planOk el r (dayPlan r) = true :=
  dayPlan_ok_of_the_core_seven hfn r
    (dayPlan_ok_core_of_plain_walls r hagree hactive hday hnowcal hwalls hpast)


/-! ############################################################################
## W-26 (track G): the FOURTH and LAST axis of the lift, and the twelfth property
############################################################################

**Three axes are closed and the fourth is not a proof.**  W-23 named the eligibility axis
(`FromNowAnchored`), W-24 the log axis (`PastPays`), W-25 the wall axis (`WallsArePlain`).
`dayPlan_ok_on_the_whole_day_of_plain_walls`'s own doc comment says what is left, and this
section gives it the name the other three have: `wallsAgree`, `activeAgrees` and `dayAgrees`
are decidable `Bool`s and `hnowcal` is one `Nat` comparison, and **all four are the request
DECODER's obligation** (README gap 346), not the planner's and not a `∀` over anything.
`DecoderPays` is that axis, and `dayPlan_ok_on_the_whole_day_of_a_paying_decoder` is §6.1's
lift with no loose hypothesis left in it.

**What naming it buys is a question with an answer.**  `PlannerWit.mkPlanReq?_ignores_state`
proves the one builder in this tree never reads `Planner.RuntimeIn` at all, so
`PlannerWit.the_builder_accepts_a_running_block_it_never_checked` turns a clause of this
structure into a counterexample rather than a hope: of the four, exactly **one**
(`PlannerWit.mkPlanReq?_ok_wallsAgree`) has a caller today.  D48 moves `state` onto the wire
in R2, and this is what that wire's decoder owes on arrival.

**And the twelfth property, which is NOT one of the eleven** (README gap 1529).  The day
this kernel produces can hold a **segment-free hole** — an instant inside the planned span
that no row covers — and nothing in `checksOf` forbids one: §8.3's list asserts no *overlap*
and says nothing about a *gap*.  `holeFree` is the statement, stated now so that the step
which deletes the fork's planner can land it, and it is deliberately **not** added to
`checksCore` or `checksEligible`: it is false today, on the day where the census is seven
(`PlannerWit.the_hole_property_is_not_one_of_the_eleven`), so adding it to the battery would
turn every lift in this file red for a defect no lift is about.

**Two legitimate cases the statement must not flag, and the second was found by computing.**
(1) A **tail remainder** — the unplanned time after the last row — is not a hole, and
`the_last_row_is_never_a_holes_subject` is why: the clause is guarded by *"some row starts
after this one stops"*, so the row with the greatest stop is never its subject.
(2) The **replayed past** is out of scope.  An instant nobody worked is genuinely unplanned
and the log, not the planner, decides it; the census day's own morning holds a 45-minute
such gap between a replayed break and the next replayed block.  So the property is stated
over `futureHalf`, the rows at or after `now` — E1's own restriction, the fork's
`assigned_set` window, which `plan_places_no_block_over_a_wall` and
`plan_places_no_block_over_a_break` already use.  `keepFromNow` is **not** that filter and is
not reused for it: `keepFromNow` keeps every non-work row whatever its instant, which is
right for the six block-side checks and wrong here, where a Rest row before `now` is exactly
the row whose absence would read as a gap. -/

/-- **The rows at or after `now`, all kinds.**  `withoutActive` above is the pattern: hand a
checker a shorter segment list rather than write a second checker.  It is **not**
`withoutPast`, which keeps a non-work row whatever its instant — see the section header. -/
def futureHalf (r : PlanReq) (d : DayPlan) : DayPlan :=
  { d with segments := d.segments.filter (fun s => decide (r.now.sec ≤ s.val.start)) }

theorem futureHalf_segments (r : PlanReq) (d : DayPlan) :
    (futureHalf r d).segments =
      d.segments.filter (fun s => decide (r.now.sec ≤ s.val.start)) := rfl

/-- A row of `futureHalf` is a row of the day, and it starts at or after `now`. -/
theorem mem_futureHalf (r : PlanReq) (d : DayPlan) (s : WfSeg)
    (h : s ∈ (futureHalf r d).segments) : s ∈ d.segments ∧ r.now.sec ≤ s.val.start := by
  rw [futureHalf_segments] at h
  obtain ⟨h1, h2⟩ := List.mem_filter.1 h
  exact ⟨h1, of_decide_eq_true h2⟩

/-- **§8.3's missing invariant, beside "no overlap"** (README gap 1529): no instant between
two rows is left uncovered.

Read it at one row `a`: *if* any row starts strictly after `a` stops, *then* some row covers
the instant `a.stop` itself.  A chain of such clauses closes every interior gap — if the
instant after `a` is covered by `c`, the same clause at `c` carries the argument forward —
while a **tail** (no row starts after `a`) satisfies it vacuously.

**D9-21**: `d.segments.all` over `d.segments.any`, quadratic in the segment list, the same
class as the four nested checkers the module header names.  Nothing on the shipped path
evaluates it. -/
def holeFree (_r : PlanReq) (d : DayPlan) : Bool :=
  d.segments.all (fun a =>
    decide ((∃ b ∈ d.segments, a.val.stop < b.val.start) →
            (∃ c ∈ d.segments, c.val.start ≤ a.val.stop ∧ a.val.stop < c.val.stop)))

theorem holeFree_iff (r : PlanReq) (d : DayPlan) :
    holeFree r d = true ↔
      ∀ a ∈ d.segments, (∃ b ∈ d.segments, a.val.stop < b.val.start) →
        ∃ c ∈ d.segments, c.val.start ≤ a.val.stop ∧ a.val.stop < c.val.stop := by
  simp only [holeFree, List.all_eq_true, decide_eq_true_eq]

/-- **A tail remainder is not a hole, and this is the reason rather than an assurance.**  The
row with the greatest stop has no row starting after it, so `holeFree`'s clause at that row
is vacuous whatever the day's end is — the statement mentions neither `PlanReq.dayEnd` nor
`DayPlan.budgetBlocks`. -/
theorem the_last_row_is_never_a_holes_subject (d : DayPlan) (a : WfSeg)
    (hmax : ∀ b ∈ d.segments, b.val.start ≤ a.val.stop) :
    ¬ ∃ b ∈ d.segments, a.val.stop < b.val.start := by
  rintro ⟨b, hb, hlt⟩
  exact absurd (hmax b hb) (Nat.not_le.2 hlt)

/-- **The other direction** (AGENTS §5.8): an inter-row break that nothing emitted makes this
check answer `false`, by name.  This is the shape a failure takes — two rows with a gap
between them and no third row covering the first one's stop. -/
theorem an_uncovered_instant_between_two_rows_is_a_hole (r : PlanReq) (d : DayPlan)
    (a b : WfSeg) (ha : a ∈ d.segments) (hb : b ∈ d.segments)
    (hgap : a.val.stop < b.val.start)
    (hunc : ∀ c ∈ d.segments, ¬ (c.val.start ≤ a.val.stop ∧ a.val.stop < c.val.stop)) :
    holeFree r d = false := by
  rcases h : holeFree r d with _ | _
  · rfl
  · exact absurd ((holeFree_iff r d).1 h a ha ⟨b, hb, hgap⟩)
      (by rintro ⟨c, hc, h1, h2⟩; exact hunc c hc ⟨h1, h2⟩)

/-- **A zero-length row cannot launder a hole**, which is the one way this statement could
have been gamed: `Planner.Seg.wf` is `start ≤ stop`, so a row of no duration is constructible,
and it covers no instant at all because the cover clause needs `t < c.stop`. -/
theorem a_zero_length_row_cannot_cover_an_instant (c : WfSeg) (hz : c.val.start = c.val.stop)
    (t : Nat) : ¬ (c.val.start ≤ t ∧ t < c.val.stop) := by
  rintro ⟨h1, h2⟩; omega

/-- **A day with no rows passes**, stated rather than left to be discovered.  `holeFree` is a
`List.all` over the rows, so it says nothing whatever about a day that has none — and nothing
about the time before the first row either (`PlannerWit.the_hole_property_is_blind_to_a
_leading_remainder` is that second blind spot as a theorem).  Coverage of the planning window
is a **different** property and this one is not it. -/
theorem holeFree_of_no_rows (r : PlanReq) (d : DayPlan) (h : d.segments = []) :
    holeFree r d = true := by simp [holeFree, h]

/-- **What the request DECODER owes §6.1's lift** — the fourth axis, named the way `PastPays`
and `WallsArePlain` name theirs.  Four clauses, none of them a `∀` over the request: three
decidable `Bool`s and one `Nat` comparison.  README gap **346** is the gap that closes it, and
`PlannerWit.mkPlanReq?_ok_wallsAgree` is the only one of the four with a caller today. -/
structure DecoderPays (r : PlanReq) : Prop where
  /-- The request's wall index is its own plan's (`PlanReq.wallsAgree`). -/
  walls  : r.wallsAgree = true
  /-- A running block the request carries is one `Planner.mkActive?` would have built
  (`PlanReq.activeAgrees`). -/
  active : r.activeAgrees = true
  /-- The `[day]` the request carries is one `Look.mkDayCfg?` would have built
  (`PlanReq.dayAgrees`). -/
  day    : r.dayAgrees = true
  /-- `now` is inside the calendar, which is what lets a clause written over the log be read
  off the row the day holds (`segOf_replayed`). -/
  nowCal : r.now.sec + 1 < LogStamp.yearEnd

/-- **§6.1's eleven on the whole day, with every axis named and no loose hypothesis left.**

Four bounds, four names: the eligibility one by `FromNowAnchored` (W-23), the log one by
`PastPays` (W-24), the wall one by `WallsArePlain` (W-25), the request one by `DecoderPays`
(here).  `dayPlan_ok_on_the_whole_day_of_plain_walls` is the same statement with the four
clauses spelled out, kept because every existing caller spells them. -/
theorem dayPlan_ok_on_the_whole_day_of_a_paying_decoder {el : Eligible}
    (hfn : FromNowAnchored el) (r : PlanReq) (hdec : DecoderPays r)
    (hwalls : WallsArePlain r (dayPlan r)) (hpast : PastPays r) :
    planOk el r (dayPlan r) = true :=
  dayPlan_ok_on_the_whole_day_of_plain_walls hfn r hdec.walls hdec.active hdec.day
    hdec.nowCal hwalls hpast


/-! ############################################################################
## W-28 (track G): the LEADING half of gap 1620, closed at the instant `futureHalf` already names
############################################################################

W-26 stated §8.3's twelfth property (`holeFree`) and recorded **three** things it cannot see:
the time before the first row (`PlannerWit.the_hole_property_is_blind_to_a_leading_remainder`,
two hours at a real request), a day with no rows at all (`holeFree_of_no_rows`), and the tail
(`the_last_row_is_never_a_holes_subject`).  README gap **1620** priced closing them as *"a
coverage property needs a **window** to cover, and which window is a decision nobody has
taken"*.

**Two of the three need no such decision, and this section takes them.**  The property is
stated over `futureHalf`, whose own filter is `r.now.sec ≤ s.val.start`; so the window's
**start** is not an open question — it is `r.now`, already chosen, already the fork's
`assigned_set` bound.  Only the window's **end** is undecided, and the tail is gap 1529's own
deliberate carve-out rather than an oversight.  So `coveredAt` closes the leading remainder at
`r.now` and, in the same clause, the empty day — `List.any` over no rows is `false` — and gap
1620 shrinks from three blind spots to one.

**Nothing is weakened and nothing is enabled.**  `holeFreeFrom` is `holeFree` conjoined with one
more clause, `holeFreeFrom_implies_holeFree` is D5's "the new implies the old", and neither is in
`checksOf`: the battery is still eleven
(`PlannerWit.the_hole_property_is_not_one_of_the_eleven`), and both are still false on the day
this kernel produces.  R3 is what enables them. -/

/-- **Some row covers the instant `t`** — the cover clause `holeFree` already writes at
`a.val.stop`, at a named instant instead.  It is not a second notion of covering: the
conjunction is the same `c.val.start ≤ t ∧ t < c.val.stop`, which is why
`a_zero_length_row_cannot_cover_an_instant` applies to this one unchanged. -/
def coveredAt (t : Nat) (d : DayPlan) : Bool :=
  d.segments.any (fun c => decide (c.val.start ≤ t ∧ t < c.val.stop))

/-- The reflection lemma. -/
theorem coveredAt_iff (t : Nat) (d : DayPlan) :
    coveredAt t d = true ↔ ∃ c ∈ d.segments, c.val.start ≤ t ∧ t < c.val.stop := by
  simp only [coveredAt, List.any_eq_true, decide_eq_true_eq]

/-- **A day with no rows covers no instant**, which is the half of W-26's second blind spot
this clause closes: `holeFree_of_no_rows` passes such a day and `coveredAt` refuses it. -/
theorem coveredAt_of_no_rows (t : Nat) (d : DayPlan) (h : d.segments = []) :
    coveredAt t d = false := by simp [coveredAt, h]

/-- **§8.3's twelfth property with its LEADING blind spot closed** — contiguity from `now`
onward, which is one clause more than `holeFree` and one clause less than coverage of a window
whose end nobody has chosen (README gap 1620).

The instant is `r.now.sec` and not a new bound: it is `futureHalf`'s own filter, E1's
restriction and the fork's `assigned_set` window, the same second three checkers already use.

**And the TAIL stays out of scope**, inherited rather than repaired: neither conjunct mentions
the day's end.  The second is `holeFree`, whose clause at the last row is vacuous
(`the_last_row_is_never_a_holes_subject`); the first is read at `r.now` alone.  So a day whose
rows run back to back from `now` and then stop passes with its whole remainder unplanned, and
`PlannerWit.the_leading_guard_keeps_the_tail_carve_out` computes such a day rather than leaving
that sentence an assurance.  It is the ONE blind spot gap 1620 has left, and it is the one gap
1529's brief asked to be kept. -/
def holeFreeFrom (r : PlanReq) (d : DayPlan) : Bool :=
  coveredAt r.now.sec d && holeFree r d

theorem holeFreeFrom_iff (r : PlanReq) (d : DayPlan) :
    holeFreeFrom r d = true ↔
      (∃ c ∈ d.segments, c.val.start ≤ r.now.sec ∧ r.now.sec < c.val.stop) ∧
      ∀ a ∈ d.segments, (∃ b ∈ d.segments, a.val.stop < b.val.start) →
        ∃ c ∈ d.segments, c.val.start ≤ a.val.stop ∧ a.val.stop < c.val.stop := by
  simp only [holeFreeFrom, Bool.and_eq_true, coveredAt_iff, holeFree_iff]

/-- **The new implies the old** (D5): nothing `holeFree` forbade is permitted here, and the
pair is not two incomparable statements.  `PlannerWit.the_leading_guard_is_not_a_constant` is
the other direction — a day the old one passes and this one refuses. -/
theorem holeFreeFrom_implies_holeFree (r : PlanReq) (d : DayPlan)
    (h : holeFreeFrom r d = true) : holeFree r d = true := by
  simp only [holeFreeFrom, Bool.and_eq_true] at h; exact h.2

/-- **And the empty day is refused**, where `holeFree_of_no_rows` passes it. -/
theorem holeFreeFrom_of_no_rows (r : PlanReq) (d : DayPlan) (h : d.segments = []) :
    holeFreeFrom r d = false := by
  simp only [holeFreeFrom, coveredAt_of_no_rows r.now.sec d h, Bool.false_and]

/-! ############################################################################
## W-29 (track G): what STEP 6 keeps, and the FIFTH thing the request decoder owes
############################################################################

**Both halves of this section are about the rows step P9 composes into the day, and neither
is about a row.**  `Planner.PlanReq.assignFold` is §8.2 step 5's assignment and
`Planner.PlanReq.assignFold_ok` is the three filter clauses it satisfies — the energy filter,
the `loc:` filter and the wind-down rule.  The rows a composition step emits are **not** read
off it: they are read off `Planner.PlanReq.finalAssign`, step **6**'s answer, exactly as
`Planner.PlanReq.restRows` already is, because fork `run()` calls `place_deferred` and then
hands `emit_segments` the same `&assign` (`planner.rs:1032`, `:1071`).

**`AssignOk` was proved for the fold and never for step 6's answer** — `deferWalk` carried
`PlacedOk`, the two lengths and `used`, and not this — so the two goals
`plan_respects_the_energy_filter` and `plan_places_no_demanding_block_after_wind_down` would
have acquired a subject at the composition and had no proof to reach for.
`finalAssign_ok` below is that proof, landed before the rows rather than after them.  It is a
**repair and not a finding**: step 6 frees a slot and re-places the displaced group through
`Planner.PlanReq.assignStep`, §8.2 step 5's own body, so the clauses survive — but surviving
and being *proved to* survive are the two things AGENTS §5.2 keeps apart.

**And the second half is a finding.**  The clauses `assignFold_ok` carries are stated over
`Planner.Group.ci`, which `Planner.groupOf` reads off `Look.Cand.ci` — the **wire's** reading
of an item's `ci`.  Every checker of this battery that asks about an item's `ci` reads
`Tm.effectiveCi r.plan.val i` — the **plan's** §3.2 inheritance walk.  Nothing in this tree
says those two agree, and `DecoderPays` does not have a clause for it.  That is E8's shape —
*two readers of an item's `ci` disagreeing about eligibility* — which is the defect
`plan_respects_the_energy_filter`'s own doc comment says it rules out, sitting in the seam
between the wire and the plan rather than inside the planner.  `candsAgree` states it, and
`PlannerWit.the_wire_ci_and_the_plan_ci_disagree_at_the_busy_request` is a request already in
this tree where it is **false**.
-/

/-- **What `AssignOk` reads of a group, as a relation between two group lists** — the fields
step 6's restore may not move.  Stated this way rather than over `Planner.unspend` by name so
that the preservation proof below is about the *rule* and not about one function: any list of
the same length whose every entry keeps the `ci` and the `loc:` of the entry it replaces will
do, and `Planner.unspend_keeps_the_group` is one such list. -/
def KeepsTheFilterFields (gs gs' : List Planner.Group) : Prop :=
  gs'.length = gs.length ∧
    ∀ (n : Nat) (g' : Planner.Group), gs'[n]? = some g' →
      ∃ g : Planner.Group, gs[n]? = some g ∧ g.ci = g'.ci ∧ g.loc = g'.loc ∧
        g.members = g'.members

theorem KeepsTheFilterFields_refl (gs : List Planner.Group) : KeepsTheFilterFields gs gs := by
  refine ⟨rfl, fun n g' h => ⟨g', h, rfl, rfl, rfl⟩⟩

/-- `Planner.unspend` keeps them, which is the one instance this section needs. -/
theorem KeepsTheFilterFields_unspend (gi mins : Nat) (gs : List Planner.Group) :
    KeepsTheFilterFields gs (unspend gi mins gs) := by
  refine ⟨unspend_length gi mins gs, fun n g' h => ?_⟩
  obtain ⟨g, hg, -, hmem, hci, hloc, -, -, -⟩ := unspend_keeps_the_group gi mins gs n g' h
  exact ⟨g, hg, hci, hloc, hmem⟩

/-- **Freeing a slot and restoring its group's minutes keeps `AssignOk`.**  Fork
`place_deferred`'s displacement (`planner.rs:1684-1704`) does exactly these two things to the
assignment before it re-places, and the clause at every *other* slot is the old clause read
through the restored group. -/
theorem AssignOk_of_freed (r : PlanReq) (a : Assign) (vi u : Nat) (gs : List Planner.Group)
    (hk : KeepsTheFilterFields a.groups gs) (h : r.AssignOk a) :
    r.AssignOk ⟨a.slotOf.set vi Option.none, gs, u⟩ := by
  obtain ⟨hlen, hcl⟩ := h
  obtain ⟨hglen, hkeep⟩ := hk
  refine ⟨by simpa using hlen, ?_⟩
  intro i gi hi
  simp only at hi
  by_cases hiv : i = vi
  · subst hiv
    by_cases hlt : i < a.slotOf.length
    · rw [List.getElem?_set_self hlt] at hi; exact absurd hi (by simp)
    · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hlt)] at hi
      exact absurd hi (by simp)
  · rw [List.getElem?_set_ne (by omega)] at hi
    obtain ⟨e, s, g, he, hg, h1, h2, h3⟩ := hcl i gi hi
    have hglt : gi < gs.length := by
      rw [hglen]; exact lt_of_getElem?_some hg
    obtain ⟨g2, hg2⟩ : ∃ g2 : Planner.Group, gs[gi]? = some g2 :=
      ⟨gs[gi]'hglt, List.getElem?_eq_getElem hglt⟩
    obtain ⟨g0, hg0, hci, hloc, -⟩ := hkeep gi g2 hg2
    rw [hg] at hg0
    have hgg : g = g0 := Option.some.inj hg0
    subst hgg
    refine ⟨e, s, g2, he, hg2, ?_, ?_, ?_⟩
    · rw [← hci]; exact h1
    · rw [← hloc]; exact h2
    · rw [← hci]; exact h3

/-- **Step 6's re-placement keeps the three clauses**, because it *is* §8.2 step 5's own loop
body: `Planner.PlanReq.rePlaceWalk` calls `Planner.PlanReq.assignStep` with the same
`todaySlots`, and `Planner.PlanReq.assignStep_ok` is already the one-step law.  Nothing is
re-derived here (AGENTS §5.3); this is the induction that the fold has and the walk did not. -/
theorem rePlaceWalk_keeps_AssignOk (r : PlanReq) (budget : Nat) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)),
      (∀ x ∈ l, r.energisedSlots[x.2]? = some x.1) →
      ∀ a : Assign, r.AssignOk a → r.AssignOk (r.rePlaceWalk budget a l) := by
  intro l
  induction l with
  | nil => intro _ a ha; exact ha
  | cons x xs ih =>
    intro hl a ha
    have hstep := PlanReq.assignStep_ok r r.todayBreaks budget a x
      (hl x (List.mem_cons_self ..)) ha
    have key : r.rePlaceWalk budget a (x :: xs)
        = if (r.assignStep r.todaySlots r.todayBreaks budget a x).used = a.used
          then r.rePlaceWalk budget (r.assignStep r.todaySlots r.todayBreaks budget a x) xs
          else r.assignStep r.todaySlots r.todayBreaks budget a x := rfl
    rw [key]
    split
    · exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) _ hstep
    · exact hstep

/-- **And so does the displacement that calls it** — the slot goes back to being free, the
group gets its minutes back, and the clause at every other slot is untouched. -/
theorem displaceInto_keeps_AssignOk (r : PlanReq) (budget : Nat) (a : Assign) (q : Placed)
    (vi : Nat) (s : Look.Slot) (ha : r.AssignOk a) :
    r.AssignOk (r.displaceInto budget a q vi s).2 := by
  unfold PlanReq.displaceInto
  refine rePlaceWalk_keeps_AssignOk r budget _
    (fun y hy => List.mem_zipIdx_iff_getElem?.mp (List.mem_of_mem_drop hy)) _ ?_
  refine AssignOk_of_freed r a vi _ _ ?_ ha
  cases h : (a.slotOf[vi]?).join with
  | none => simp only [h]; exact KeepsTheFilterFields_refl a.groups
  | some gi => simp only [h]; exact KeepsTheFilterFields_unspend gi s.minutes a.groups

/-- **One instance of step 6 keeps them**: four of `Planner.PlanReq.deferOne`'s five outcomes
hand the assignment back unchanged, and the fifth is the displacement above. -/
theorem deferOne_keeps_AssignOk (r : PlanReq) (budget : Nat) (qs : List Placed) (a : Assign)
    (q : Placed) (ha : r.AssignOk a) : r.AssignOk (r.deferOne budget qs a q).2 := by
  unfold PlanReq.deferOne
  repeat' split
  all_goals first
    | exact ha
    | exact displaceInto_keeps_AssignOk r budget a q _ _ ha

/-- **And so does the whole walk.** -/
theorem deferWalk_keeps_AssignOk (r : PlanReq) (budget : Nat) :
    ∀ (post pre : List Placed) (a : Assign),
      r.AssignOk a → r.AssignOk (r.deferWalk budget pre a post).2 := by
  intro post
  induction post with
  | nil => intro pre a ha; exact ha
  | cons q rest ih =>
    intro pre a ha
    unfold PlanReq.deferWalk
    exact ih _ _ (deferOne_keeps_AssignOk r budget _ a q ha)

/-- **§8.2 step 5's energy filter, `loc:` filter and wind-down rule hold of STEP 6's
assignment** — the one `Planner.PlanReq.restRows` reads and the one a composition step's rows
must read, for the reason `restRows`' doc comment gives (fork `run()` calls `place_deferred`
and then hands `emit_segments` the same `&assign`).

`Planner.PlanReq.assignFold_ok` is this at step 5's answer; this is the same three clauses one
step later.  **It is the proof `plan_respects_the_energy_filter` and
`plan_places_no_demanding_block_after_wind_down` reach for once a slot emits a row**, and it is
here before the rows are, so that the composition step lands against a proved invariant rather
than acquiring a subject and an obligation in the same commit. -/
theorem finalAssign_ok (r : PlanReq) : r.AssignOk r.finalAssign := by
  unfold PlanReq.finalAssign PlanReq.deferFold
  exact deferWalk_keeps_AssignOk r _ r.placedRoutines [] r.assignFold (PlanReq.assignFold_ok r)

/-- **The clause at one slot, spelled out** — what a Block row at slot `i` may assume about the
group that holds it, with no `Planner.Assign` in the statement. -/
theorem an_assigned_slot_is_under_its_slots_energy (r : PlanReq) (i gi : Nat)
    (h : r.finalAssign.slotOf[i]? = some (some gi)) (e : Fin 6) (s : Look.Slot)
    (hes : r.energisedSlots[i]? = some (e, s)) (g : Planner.Group)
    (hg : r.finalAssign.groups[gi]? = some g) :
    g.ci.val ≤ e.val ∧ ¬ (r.windDownSec ≤ s.start ∧ 4 ≤ g.ci.val) := by
  obtain ⟨-, hcl⟩ := finalAssign_ok r
  obtain ⟨e', s', g', he', hg', h1, -, h3⟩ := hcl i gi h
  rw [hes] at he'
  have hp : (e, s) = (e', s') := Option.some.inj he'
  rw [Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  rw [hg] at hg'
  have hgg : g = g' := Option.some.inj hg'
  subst hgg
  exact ⟨h1, h3⟩

/-! ### The group a filled slot names, one step later

`Planner.PlanReq.an_assigned_slot_names_a_group` is this at §8.2 step 5's answer.  Step 6 is
two more ways a group list can change — `Planner.PlanReq.assignStep` again, and
`Planner.unspend` — and both of them keep exactly the fields `KeepsTheFilterFields` names, so
the provenance is carried by transitivity rather than by a third induction over the fork's
loop body. -/

theorem KeepsTheFilterFields_trans {gs gs' gs'' : List Planner.Group}
    (h1 : KeepsTheFilterFields gs gs') (h2 : KeepsTheFilterFields gs' gs'') :
    KeepsTheFilterFields gs gs'' := by
  refine ⟨h2.1.trans h1.1, fun n g'' h => ?_⟩
  obtain ⟨g', hg', hc, hl, hm⟩ := h2.2 n g'' h
  obtain ⟨g, hg, hc2, hl2, hm2⟩ := h1.2 n g' hg'
  exact ⟨g, hg, hc2.trans hc, hl2.trans hl, hm2.trans hm⟩

theorem KeepsTheFilterFields_assignStep (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat) :
    KeepsTheFilterFields a.groups (r.assignStep slots breaks budget a x).groups := by
  refine ⟨(PlanReq.assignStep_lengths r slots breaks budget a x).2, fun n g' h => ?_⟩
  obtain ⟨g, hg, -, hm, hc, hl, -, -⟩ :=
    PlanReq.assignStep_keeps_the_group r slots breaks budget a x n g' h
  exact ⟨g, hg, hc, hl, hm⟩

theorem KeepsTheFilterFields_rePlaceWalk (r : PlanReq) (budget : Nat) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a : Assign),
      KeepsTheFilterFields a.groups (r.rePlaceWalk budget a l).groups := by
  intro l
  induction l with
  | nil => intro a; exact KeepsTheFilterFields_refl a.groups
  | cons x xs ih =>
    intro a
    have key : r.rePlaceWalk budget a (x :: xs)
        = if (r.assignStep r.todaySlots r.todayBreaks budget a x).used = a.used
          then r.rePlaceWalk budget (r.assignStep r.todaySlots r.todayBreaks budget a x) xs
          else r.assignStep r.todaySlots r.todayBreaks budget a x := rfl
    rw [key]
    split
    · exact KeepsTheFilterFields_trans
        (KeepsTheFilterFields_assignStep r r.todaySlots r.todayBreaks budget a x) (ih _)
    · exact KeepsTheFilterFields_assignStep r r.todaySlots r.todayBreaks budget a x

theorem KeepsTheFilterFields_displaceInto (r : PlanReq) (budget : Nat) (a : Assign)
    (q : Placed) (vi : Nat) (s : Look.Slot) :
    KeepsTheFilterFields a.groups (r.displaceInto budget a q vi s).2.groups := by
  unfold PlanReq.displaceInto
  refine KeepsTheFilterFields_trans ?_ (KeepsTheFilterFields_rePlaceWalk r budget _ _)
  cases h : (a.slotOf[vi]?).join with
  | none => simp only [h]; exact KeepsTheFilterFields_refl a.groups
  | some gi => simp only [h]; exact KeepsTheFilterFields_unspend gi s.minutes a.groups

theorem KeepsTheFilterFields_deferOne (r : PlanReq) (budget : Nat) (qs : List Placed)
    (a : Assign) (q : Placed) :
    KeepsTheFilterFields a.groups (r.deferOne budget qs a q).2.groups := by
  unfold PlanReq.deferOne
  repeat' split
  all_goals first
    | exact KeepsTheFilterFields_refl a.groups
    | exact KeepsTheFilterFields_displaceInto r budget a q _ _

theorem KeepsTheFilterFields_deferWalk (r : PlanReq) (budget : Nat) :
    ∀ (post pre : List Placed) (a : Assign),
      KeepsTheFilterFields a.groups (r.deferWalk budget pre a post).2.groups := by
  intro post
  induction post with
  | nil => intro pre a; exact KeepsTheFilterFields_refl a.groups
  | cons q rest ih =>
    intro pre a
    unfold PlanReq.deferWalk
    exact KeepsTheFilterFields_trans (KeepsTheFilterFields_deferOne r budget _ a q) (ih _ _)

theorem KeepsTheFilterFields_foldl_assignStep (r : PlanReq) (breaks : List (Nat × Nat))
    (budget : Nat) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a : Assign),
      KeepsTheFilterFields a.groups
        (l.foldl (r.assignStep r.todaySlots breaks budget) a).groups := by
  intro l
  induction l with
  | nil => intro a; exact KeepsTheFilterFields_refl a.groups
  | cons x xs ih =>
    intro a
    simp only [List.foldl_cons]
    exact KeepsTheFilterFields_trans
      (KeepsTheFilterFields_assignStep r r.todaySlots breaks budget a x) (ih _)

/-- **Every group of the day's own assignment carries the members and the `ci` of a group
`build_groups` built.**  Stated as a property of the group *list* so that the one proof serves
both walks. -/
def CarriesBuiltGroups (r : PlanReq) (gs : List Planner.Group) : Prop :=
  ∀ (n : Nat) (g : Planner.Group), gs[n]? = some g →
    ∃ g₀ ∈ r.buildGroups, g₀.members = g.members ∧ g₀.ci = g.ci

theorem CarriesBuiltGroups_of_keeps (r : PlanReq) (gs gs' : List Planner.Group)
    (hk : KeepsTheFilterFields gs gs') (h : CarriesBuiltGroups r gs) :
    CarriesBuiltGroups r gs' := by
  intro n g' hg'
  obtain ⟨g, hg, hc, -, hm⟩ := hk.2 n g' hg'
  obtain ⟨g₀, h0, m0, c0⟩ := h n g hg
  exact ⟨g₀, h0, m0.trans hm, c0.trans hc⟩

theorem CarriesBuiltGroups_startGroups (r : PlanReq) : CarriesBuiltGroups r r.startGroups := by
  intro n g hg
  obtain ⟨g₀, h0, -, hm, hc, -, -, -⟩ :=
    PlanReq.a_started_group_is_a_built_group (List.mem_of_getElem? hg)
  exact ⟨g₀, h0, hm.symm, hc.symm⟩

/-- **And step 6's answer carries them too** — the fold and the walk composed. -/
theorem CarriesBuiltGroups_finalAssign (r : PlanReq) :
    CarriesBuiltGroups r r.finalAssign.groups := by
  have h1 : KeepsTheFilterFields r.startGroups r.assignFold.groups := by
    unfold PlanReq.assignFold
    exact KeepsTheFilterFields_foldl_assignStep r r.todayBreaks (remainingBudget r) _
      r.assignStart
  have h2 : KeepsTheFilterFields r.assignFold.groups r.finalAssign.groups := by
    unfold PlanReq.finalAssign PlanReq.deferFold
    exact KeepsTheFilterFields_deferWalk r _ r.placedRoutines [] r.assignFold
  exact CarriesBuiltGroups_of_keeps r _ _ h2
    (CarriesBuiltGroups_of_keeps r _ _ h1 (CarriesBuiltGroups_startGroups r))

/-- **A member of a group that holds a slot carries that group's `ci`** — §7.5's batching
gathers by equal `ci` and `Planner.splitGroups` does not change it, so `Planner.Group.ci` is a
bound over the members and not just the head's value.  This is the step-6 form of
`Planner.PlanReq.a_group_member_carries_the_groups_ci`. -/
theorem a_member_of_an_assigned_group_carries_its_ci (r : PlanReq) (gi : Nat)
    (g : Planner.Group) (hg : r.finalAssign.groups[gi]? = some g) (m : Ranked)
    (hm : m ∈ g.members) : m.cand.ci = g.ci := by
  obtain ⟨g₀, h0, hmem, hci⟩ := CarriesBuiltGroups_finalAssign r gi g hg
  rw [← hci]
  exact PlanReq.a_group_member_carries_the_groups_ci h0 (hmem ▸ hm)

/-! ### The FIFTH thing the request decoder owes, and it is not a fifth item on a list

`DecoderPays` has four clauses because four *values* of a `Planner.PlanReq` reach §6.1's lift
without anything having checked them.  The rule that put them there is not "these four": it is
**every value the battery reads off the request rather than off the day**.  Read that way the
list was short, and what it was missing is the one the composition step needs.

**The rule, applied.**  Grep this file for `r.plan.val` and every hit is a checker reading an
item's facts out of the *plan*: `Tm.effectiveCi` (`energyFilterOk`, `noDemandingAfterWindDown`,
`monotoneInRank`, `batchDoesNotReachPast`), `Tm.rootPrio` (`monotoneInRank`), the `hot` flag
(`hotBeforeQueue`), `Field.Shape.interval` (`wallsUnmoved`).  §8.2 step 5's fold reads the same
item's facts out of `Look.Cand` — `Planner.groupOf` takes `x.cand.ci` for the group's `ci`,
§7.4's key is built on `Look.Cand.rootPrio`, §7.2's `hot` is `Look.Cand.hot`.  **Nothing in
this tree says the two readings agree**, and `Tm.effectiveCi` of an id the store does not hold
answers `3` rather than refusing, so a candidate that is not an item of its own plan is
silently given the default.

**That is E8's shape** — *two readers of an item's `ci` disagreeing about eligibility* — which
is the defect `plan_respects_the_energy_filter`'s own doc comment says it rules out, sitting in
the seam between the wire and the plan rather than inside the planner.

**`candsAgree` is an enumeration a candidate must JOIN to be exempt** (W-27's shape, and the
one this campaign is now required to take): `candPlanView` answers `none` for an id the store
does not hold, `none = some _` is false, and the clause therefore **fails by name** on such a
candidate rather than passing it on a default.  There is no allow-list. -/

/-- **The plan's reading of a candidate**: the three values this battery reads off the store
when it asks about an item.  `none` when the store does not hold the id at all. -/
def candPlanView (r : PlanReq) (i : Id) : Option (Fin 6 × Option (Fin 4) × Bool) :=
  match r.plan.val.store.get i with
  | none => none
  | some e => some (effectiveCi r.plan.val i, rootPrio r.plan.val i,
      decide (Flag.hot ∈ e.val.flags))

/-- **The wire's reading of the same three**, as `Look.Cand` carries them and §8.2 step 5's
fold reads them. -/
def candWireView (c : Look.Cand) : Fin 6 × Option (Fin 4) × Bool := (c.ci, c.rootPrio, c.hot)

/-- **The fifth clause of the decoder axis** (README gap **1984**): every candidate the request
carries is an item of the request's own plan, and its wire-side `ci`, `rootPrio` and `hot` are
that item's.

**WHAT THIS DOES NOT COVER, said here rather than found later** (README gap **1990**).  The
rule is *every value the battery reads off the request rather than off the day*, and this
clause is that rule restricted to the values `Look.Cand` **carries**.  The battery also reads
`e.val.live.doc` and `e.val.live.rank` off the store — `monotoneInRank` and
`batchDoesNotReachPast` both do — and `Look.Cand` has no rank field at all: §7.4's key is built
from the candidate list's **order**.  So a second disagreement axis exists, between the store's
`live.rank` and the wire list's position, and no clause here states it.  It is not this
clause's business and it is not `WallsArePlain`'s either; it is a sixth thing the decoder owes,
and it bites `plan_is_monotone_in_rank`'s restatement rather than
`plan_respects_the_energy_filter`. -/
def candsAgree (r : PlanReq) : Bool :=
  r.cands.val.all (fun p => decide (candPlanView r p.1.id = some (candWireView p.1)))

theorem candsAgree_iff (r : PlanReq) :
    candsAgree r = true ↔
      ∀ p ∈ r.cands.val, candPlanView r p.1.id = some (candWireView p.1) := by
  simp only [candsAgree, List.all_eq_true, decide_eq_true_eq]

/-- **A request with no candidate pays it for nothing**, which is why nine runs of witnesses
never met it: every request whose day the eleven have been lifted over sends candidates the
fold cannot place, or none at all. -/
theorem candsAgree_of_no_cands (r : PlanReq) (h : r.cands.val = []) : candsAgree r = true := by
  simp [candsAgree, h]

/-- **What the clause buys, at one candidate**: the `ci` §8.2 step 5's filter compared against
the slot's energy *is* the `ci` `energyFilterOk` reads. -/
theorem a_candidates_ci_is_its_items_ci (r : PlanReq) (h : candsAgree r = true)
    (c : Look.Cand) (f : Option Look.Floor) (hc : (c, f) ∈ r.cands.val) :
    effectiveCi r.plan.val c.id = c.ci := by
  have hv := (candsAgree_iff r).1 h (c, f) hc
  unfold candPlanView at hv
  cases hs : r.plan.val.store.get c.id with
  | none => rw [hs] at hv; exact absurd hv (by simp)
  | some e =>
    rw [hs] at hv
    simp only [Option.some.injEq, candWireView, Prod.mk.injEq] at hv
    exact hv.1

/-- **And the other direction** (AGENTS §5.8): one candidate whose two readings differ makes
the clause `false`, by name. -/
theorem a_candidate_whose_two_readings_differ_breaks_the_clause (r : PlanReq)
    (c : Look.Cand) (f : Option Look.Floor) (hc : (c, f) ∈ r.cands.val)
    (hne : effectiveCi r.plan.val c.id ≠ c.ci) : candsAgree r = false := by
  cases h : candsAgree r with
  | false => rfl
  | true => exact absurd (a_candidates_ci_is_its_items_ci r h c f hc) hne

/-- **§8.2 step 5's energy filter, at the `ci` the battery reads** — the content of
`plan_respects_the_energy_filter`, proved at the assignment before any row exists.

Three facts compose: `finalAssign_ok` (step 6 keeps the filter),
`a_member_of_an_assigned_group_carries_its_ci` (the group's `ci` bounds every member) and the
fifth decoder clause (the member's wire `ci` is its item's).  **The last is the only one that
is not a theorem about this kernel**, which is exactly why it belongs beside `DecoderPays`'
other four and not inside the planner. -/
theorem an_assigned_member_is_under_its_slots_energy (r : PlanReq) (hca : candsAgree r = true)
    (i gi : Nat) (h : r.finalAssign.slotOf[i]? = some (some gi)) (e : Fin 6) (s : Look.Slot)
    (hes : r.energisedSlots[i]? = some (e, s)) (g : Planner.Group)
    (hg : r.finalAssign.groups[gi]? = some g) (m : Ranked) (hm : m ∈ g.members)
    (f : Option Look.Floor) (hmc : (m.cand, f) ∈ r.cands.val) :
    (effectiveCi r.plan.val m.cand.id).val ≤ e.val := by
  rw [a_candidates_ci_is_its_items_ci r hca m.cand f hmc,
    a_member_of_an_assigned_group_carries_its_ci r gi g hg m hm]
  exact (an_assigned_slot_is_under_its_slots_energy r i gi h e s hes g hg).1

/-- **And §8.2 step 5's wind-down rule at the same `ci`** — the content of
`plan_places_no_demanding_block_after_wind_down`, on the same three facts. -/
theorem an_assigned_member_after_the_wind_down_is_not_demanding (r : PlanReq)
    (hca : candsAgree r = true) (i gi : Nat)
    (h : r.finalAssign.slotOf[i]? = some (some gi)) (e : Fin 6) (s : Look.Slot)
    (hes : r.energisedSlots[i]? = some (e, s)) (hwd : r.windDownSec ≤ s.start)
    (g : Planner.Group) (hg : r.finalAssign.groups[gi]? = some g) (m : Ranked)
    (hm : m ∈ g.members) (f : Option Look.Floor) (hmc : (m.cand, f) ∈ r.cands.val) :
    (effectiveCi r.plan.val m.cand.id).val < 4 := by
  rw [a_candidates_ci_is_its_items_ci r hca m.cand f hmc,
    a_member_of_an_assigned_group_carries_its_ci r gi g hg m hm]
  have h3 := (an_assigned_slot_is_under_its_slots_energy r i gi h e s hes g hg).2
  omega

end PlanCheck
end Tm
