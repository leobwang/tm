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
day both, so at that request `checksCore` is **five of seven** and not four.  The other two
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
  rcases ht with (((ht | ht) | ht) | ht) | ht
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

end PlanCheck
end Tm
