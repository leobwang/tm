import TmKernel.Planner
/-!
# §8.2's day, each view computed once — the compiled twin of `Planner.dayPlan`

Stage 6, run W-42, track S: the owner's **D82** (README gaps 4150 and 4152) — the kernel
planner is made fast before R3.

## Why the day cost a second

`Planner.lean` states §8.2 as **views of the request**: `PlanReq.candAnswers`,
`PlanReq.startGroups`, `PlanReq.todayCut`, `PlanReq.assignFold`, `PlanReq.deferFold`, `dayRows`
are each a function of `r` and nothing else, and every reader calls the one it needs.  That is
the shape the laws are proved over, and it is the right one for them.  It is also a program that
computes the same value again at every reader, and the readers nest: a call to `Planner.dayPlan`
on §4.3's example tree computed `Look.lookahead` **805** times, `PlanReq.assignFold` 711 times,
`PlanReq.placementFold` about 4,500 times and `Cal.instantOf` 213,749 times (callgrind, W-42 track
S's block in `kernel/README.md`) — about a second a call, and nine on a tree whose lookahead runs
to 3,652 days.

## What this module is

`dayPlanOnce` computes every view the day reads more than once **exactly once** — the
`Memo`, built by `Memo.of` in §8.2's own order — and assembles the day from those values.
Each binding is the body of the view it replaces, with the views it reads replaced by the
values already computed; the step functions whose only request-dependence is a view
(`PlanReq.groupFitsSlot`, `PlanReq.assignStep`, `PlanReq.deferOne`) are written once more over
those values (`groupFitsAt`, `assignStepAt`, `deferOneAt`), and the two hand-written recursions
(`PlanReq.rePlaceWalk`, `PlanReq.deferWalk`) are their own recursion over a step
(`walkRePlace`, `walkDefer`).

**It is not a second planner.**  `dayPlanOnce_eq` proves it IS `Planner.dayPlan`, on every
request, and the `@[csimp]` lemma `dayPlan_eq_dayPlanOnce` hands that proof to the compiler, so
every definition compiled where this module is imported runs the twin and every theorem stated
over `Planner.dayPlan` is about what runs.  It is AGENTS §5.3's compiled-twin shape: the
specification and the body the export runs, one equation between them.

**Where it is imported, and why only there.**  `PlanWire.lean` imports it, so
`PlanWire.runPlanner`'s `Planner.dayPlan req` runs the twin.  `PlanDiff.lean` does NOT, so
`Planner.overtimeDiff` — §9.1's what-if, two days — still runs the specification: check 12
(`kernel/reach.py`, owner D51) requires every emitted definition to be reached from the export,
`reach-exempt.txt` may only shrink, and `Planner.dayPlan` with every view below it is reached
today only through `PlanWire.runPlanner` and `Planner.overtimeDiff`.  Were both to see this
lemma, the specification would be emitted and called by nothing.  README gap 4200 records the
cost and the lever.
-/

namespace Tm
namespace Planner

/-! ## The two recursions, over their step -/

/-- **`PlanReq.rePlaceWalk`'s recursion, over its step** (fork `place_deferred`'s re-placement):
walk forward from the slot step 6 freed, and stop at the first step that commits a block — the
loop the original writes around `PlanReq.assignStep`, with the step handed in. -/
def walkRePlace (step : Assign → ((Fin 6 × Look.Slot) × Nat) → Assign) :
    Assign → List ((Fin 6 × Look.Slot) × Nat) → Assign
  | a, [] => a
  | a, x :: rest =>
    let a' := step a x
    if a'.used = a.used then walkRePlace step a' rest else a'

theorem walkRePlace_nil (step : Assign → ((Fin 6 × Look.Slot) × Nat) → Assign) (a : Assign) :
    walkRePlace step a [] = a := rfl

theorem walkRePlace_cons (step : Assign → ((Fin 6 × Look.Slot) × Nat) → Assign) (a : Assign)
    (x : (Fin 6 × Look.Slot) × Nat) (rest : List ((Fin 6 × Look.Slot) × Nat)) :
    walkRePlace step a (x :: rest) =
      if (step a x).used = a.used then walkRePlace step (step a x) rest else step a x := rfl

/-- **It is `PlanReq.rePlaceWalk`, at that walk's own step** — both recursions unfolded a step at
a time, so the law reads the definition and not only its two equations above. -/
theorem walkRePlace_eq (r : PlanReq) (budget : Nat)
    (step : Assign → ((Fin 6 × Look.Slot) × Nat) → Assign)
    (h : ∀ a x, step a x = r.assignStep r.todaySlots r.todayBreaks budget a x) :
    ∀ (a : Assign) (xs : List ((Fin 6 × Look.Slot) × Nat)),
      walkRePlace step a xs = r.rePlaceWalk budget a xs
  | a, [] => by simp only [walkRePlace, PlanReq.rePlaceWalk]
  | a, x :: rest => by
    simp only [walkRePlace, PlanReq.rePlaceWalk, h a x]
    split
    · exact walkRePlace_eq r budget step h _ rest
    · rfl

/-- **`PlanReq.deferWalk`'s recursion, over its step** (fork `place_deferred`'s walk over the
deferred instances): each instance stepped with the whole list beside it, its predecessors as
they now stand and its successors as they were — `PlanReq.deferWalk`'s own walk, step handed in. -/
def walkDefer (step : List Placed → Assign → Placed → Placed × Assign) :
    List Placed → Assign → List Placed → List Placed × Assign
  | pre, a, [] => (pre.reverse, a)
  | pre, a, q :: post =>
    let e := step (pre.reverse ++ q :: post) a q
    walkDefer step (e.1 :: pre) e.2 post

theorem walkDefer_nil (step : List Placed → Assign → Placed → Placed × Assign)
    (pre : List Placed) (a : Assign) : walkDefer step pre a [] = (pre.reverse, a) := rfl

theorem walkDefer_cons (step : List Placed → Assign → Placed → Placed × Assign)
    (pre : List Placed) (a : Assign) (q : Placed) (post : List Placed) :
    walkDefer step pre a (q :: post) =
      walkDefer step ((step (pre.reverse ++ q :: post) a q).1 :: pre)
        (step (pre.reverse ++ q :: post) a q).2 post := rfl

/-- **It is `PlanReq.deferWalk`, at that walk's own step** — both recursions unfolded a step at a
time. -/
theorem walkDefer_eq (r : PlanReq) (budget : Nat)
    (step : List Placed → Assign → Placed → Placed × Assign)
    (h : ∀ qs a q, step qs a q = r.deferOne budget qs a q) :
    ∀ (pre : List Placed) (a : Assign) (post : List Placed),
      walkDefer step pre a post = r.deferWalk budget pre a post
  | pre, a, [] => by simp only [walkDefer, PlanReq.deferWalk]
  | pre, a, q :: post => by
    simp only [walkDefer, PlanReq.deferWalk, h]
    exact walkDefer_eq r budget step h _ _ post

/-! ## §8.2 step 5's filter and step, over values already computed -/

/-- **`PlanReq.groupFitsSlot`, its two request reads given** — `r.curLoc` as `loc` and
`r.windDownSec` as `wd`.  The original reads the wind-down (a `Cal.instantOf`) once per group
per slot per step; this reads it once a day. -/
def groupFitsAt (loc : Field.Loc) (wd : Nat) (slots : List Look.Slot) (slotOf : List (Option Nat))
    (breaks : List (Nat × Nat)) (i : Nat) (e : Fin 6) (s : Look.Slot) (g : Group) : Bool :=
  g.live && decide (g.ci.val ≤ e.val) && groupLocOk loc g.loc &&
    !(decide (wd ≤ s.start) && decide (4 ≤ g.ci.val)) &&
    (g.splittable || contiguousFits slots slotOf breaks i g.leftMin)

theorem groupFitsAt_eq (r : PlanReq) :
    groupFitsAt r.curLoc r.windDownSec = r.groupFitsSlot := rfl

/-- **`PlanReq.assignStep`, over `groupFitsAt`.** -/
def assignStepAt (loc : Field.Loc) (wd : Nat) (slots : List Look.Slot) (breaks : List (Nat × Nat))
    (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat) : Assign :=
  if (a.slotOf[x.2]?).join.isSome || decide (budget ≤ a.used) then a
  else
    match a.groups.findIdx? (groupFitsAt loc wd slots a.slotOf breaks x.2 x.1.1 x.1.2) with
    | Option.none => a
    | some gi =>
      match a.groups[gi]? with
      | Option.none => a
      | some g =>
        ⟨a.slotOf.set x.2 (some gi),
         a.groups.set gi { g with spent := g.spent + x.1.2.minutes }, a.used + 1⟩

theorem assignStepAt_eq (r : PlanReq) :
    assignStepAt r.curLoc r.windDownSec = r.assignStep := rfl

/-! ## The values §8.2 reads more than once -/

/-- **What the day reads more than once, each computed once**, named for the view it is. -/
structure Memo where
  /-- `PlanReq.windDownSec`. -/
  wd     : Nat
  /-- `PlanReq.night`. -/
  night  : Nat × Nat
  /-- `PlanReq.window`. -/
  win    : Nat × Nat
  /-- `remainingBudget`. -/
  bud    : Nat
  /-- `PlanReq.curLoc`. -/
  loc    : Field.Loc
  /-- `PlanReq.candAnswers` — §7's pass over the lookahead, the whole of step 4. -/
  ca     : List Look.FloorOut
  /-- `dayPriorities`. -/
  pri    : Capped (Id × Fin 8)
  /-- `PlanReq.activeRun`. -/
  ar     : Option ActiveRes
  /-- `PlanReq.rankedCands`. -/
  ranked : List Ranked
  /-- `PlanReq.buildGroups`. -/
  groups : List Group
  /-- `PlanReq.startGroups`. -/
  sg     : List Group
  /-- `PlanReq.placementFold` — step 2. -/
  pf     : List Placed × List (Nat × Nat)
  /-- `PlanReq.todayCut` — step 3. -/
  cut    : Look.Cut
  /-- `PlanReq.energisedSlots`. -/
  es     : List (Fin 6 × Look.Slot)
  /-- `PlanReq.assignFold` — step 5. -/
  af     : Assign
  /-- `PlanReq.keptBreaksToday`. -/
  kb     : List (Nat × Nat)

/-- **The memo, in §8.2's order.**  Each binding is the body of the view its field names, with
the views that body reads replaced by the bindings above it. -/
def Memo.of (r : PlanReq) : Memo :=
  let de := r.dayEnd
  let wd := r.windDownSec
  let night : Nat × Nat := (min wd de, de + 86400)
  let win := r.window
  let bud := remainingBudget r
  let loc := r.curLoc
  let ca := r.candAnswers
  let pri : Capped (Id × Fin 8) := ⟨ca.filterMap prioRow, (dayPriorities r).property⟩
  let ar := r.activeRun
  let ranked := sortRanked ((ca.zipIdx.filter (fun x => entersTheOrder x.1)).map
    (fun x => ⟨r.keyOf x.2 x.1, x.1⟩))
  let groups := sortGroups ((batches r.prio.batchMaxMin r.blockMin ranked).flatMap (fun b =>
    (splitGroups (ar.map (·.id)) (batchMembers b)).filterMap (fun e => groupOf e.1 e.2)))
  let sg := match ar with
    | none => groups
    | some q => spendActive q.id (Look.spanMinutes q.start q.stop) groups
  let pf := r.placementFold
  let cut := Look.cutSlots r.look.day.cut (min (max r.now.sec win.1) win.2) win.2
    (night :: pf.2) (pf.1.reverse.filterMap (·.placedAt)) r.sinceBreak
  let es := Look.energizeToday r.look cut.slots
  let af := es.zipIdx.foldl (assignStepAt loc wd cut.slots cut.breaks bud)
    ⟨List.replicate cut.slots.length Option.none, sg, if ar.isSome then 1 else 0⟩
  let kb := cut.breaks.filter (fun b =>
    (cut.slots.zip af.slotOf).any
      (fun p => p.2.isSome && (decide (p.1.stop = b.1) || decide (p.1.start = b.2))))
  ⟨wd, night, win, bud, loc, ca, pri, ar, ranked, groups, sg, pf, cut, es, af, kb⟩

/-- **Every field is the view it is named for** — one `rfl`: the memo is the views, computed
once, and nothing else. -/
theorem Memo.of_eq (r : PlanReq) :
    Memo.of r = ⟨r.windDownSec, r.night, r.window, remainingBudget r, r.curLoc, r.candAnswers,
      dayPriorities r, r.activeRun, r.rankedCands, r.buildGroups, r.startGroups, r.placementFold,
      r.todayCut, r.energisedSlots, r.assignFold, r.keptBreaksToday⟩ := rfl

/-! ## §8.2 step 6, over the memo -/

/-- **`PlanReq.deferOne`, over the memo** — the occupied list, the kept breaks, the night, the
victim search and the re-place walk each read from `m`, which `PlanReq.deferOne` recomputed for
every deferred instance (the whole of step 5 again, through `PlanReq.keptBreaksToday`). -/
def deferOneAt (r : PlanReq) (m : Memo) (qs : List Placed) (a : Assign) (q : Placed) :
    Placed × Assign :=
  if q.placedAt.isSome then (q, a)
  else if q.span.2 ≤ max q.span.1 r.now.sec then (q, a)
  else
    match r.lowestFree (m.pf.2 ++ qs.filterMap (·.placedAt) ++
              (m.cut.slots.zip a.slotOf).filterMap
                (fun p => if p.2.isSome then some (p.1.start, p.1.stop) else none) ++
              m.kb ++ [m.night])
            (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) with
    | some t => (placeAt q t, a)
    | none =>
      if q.inst.mandatory = false then (q, a)
      else
        match r.lowestFree (m.pf.2 ++ qs.filterMap (·.placedAt) ++
                  (m.cut.slots.zip a.slotOf).filterMap
                    (fun p => if p.2.isSome then some (p.1.start, p.1.stop) else none) ++
                  m.kb)
                (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) with
        | some t => (placeAt q t, a)
        | none =>
          match (leastBy victimLt
              ((m.es.zipIdx.filter (fun x =>
                  (a.slotOf[x.2]?).join.isSome && decide (max q.span.1 r.now.sec ≤ x.1.2.start) &&
                    decide (x.1.2.stop ≤ q.span.2) &&
                    decide (60 * q.inst.durMin ≤ x.1.2.stop - x.1.2.start))).map
                (fun x => (x.1.1.val, x.2)))).map Prod.snd with
          | none => (q, a)
          | some vi =>
            match m.es[vi]? with
            | none => (q, a)
            | some es =>
              (placeAt q es.2.start,
               walkRePlace (assignStepAt m.loc m.wd m.cut.slots m.cut.breaks m.bud)
                 ⟨a.slotOf.set vi Option.none,
                  (match (a.slotOf[vi]?).join with
                   | none => a.groups
                   | some gi => unspend gi es.2.minutes a.groups),
                  a.used - 1⟩
                 (m.es.zipIdx.drop (vi + 1)))

/-- **The re-place walk over the memo is `PlanReq.rePlaceWalk`.** -/
theorem walkRePlace_at (r : PlanReq) (b : Nat) :
    walkRePlace (assignStepAt r.curLoc r.windDownSec r.todayCut.slots r.todayCut.breaks b) =
      r.rePlaceWalk b := by
  funext a xs
  exact walkRePlace_eq r b _ (fun _ _ => rfl) a xs

/-- **`deferOneAt` over the views is `PlanReq.deferOne`.** -/
theorem deferOneAt_eq (r : PlanReq) (qs : List Placed) (a : Assign) (q : Placed) :
    deferOneAt r (Memo.of r) qs a q = r.deferOne (remainingBudget r) qs a q := by
  rw [Memo.of_eq]
  unfold deferOneAt
  rw [walkRePlace_at]
  rfl

/-- **An instance step 6 is handed unplaced, with time left in its window, takes the lowest free
position the memo's occupied list leaves it** — the first branch of `PlanReq.deferOne`, read off
the memo: the routines step 2 placed and the walls before them (`m.pf`), the instances already
re-placed (`qs`), the slots step 5 assigned, the kept breaks and the night. -/
theorem deferOneAt_takes_the_lowest_free (r : PlanReq) (m : Memo) (qs : List Placed) (a : Assign)
    (q : Placed) (t : Nat) (h1 : q.placedAt.isSome = false)
    (h2 : ¬ q.span.2 ≤ max q.span.1 r.now.sec)
    (h3 : r.lowestFree (m.pf.2 ++ qs.filterMap (·.placedAt) ++
        (m.cut.slots.zip a.slotOf).filterMap
          (fun p => if p.2.isSome then some (p.1.start, p.1.stop) else none) ++
        m.kb ++ [m.night]) (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) = some t) :
    deferOneAt r m qs a q = (placeAt q t, a) := by
  unfold deferOneAt
  rw [if_neg (by simp [h1]), if_neg h2, h3]

/-! ## The day, assembled from the memo and step 6 -/

/-- **`Planner.dayPlan`, from the memo `m` and step 6's result `df`** — `dayRows` and
`dayDiagnostics` with every view they read taken from `m` and `df`.  Each binding is the view
named in its comment. -/
def dayPlanFrom (r : PlanReq) (m : Memo) (df : List Placed × Assign) : DayPlan :=
  let fr := df.1
  let fa := df.2
  -- `PlanReq.emitKeptBreaks`
  let ekb := (m.cut.breaks.filter (fun b =>
      (m.cut.slots.zip fa.slotOf).any
        (fun p => p.2.isSome && (decide (p.1.stop = b.1) || decide (p.1.start = b.2))))).filter
    (fun b => !overlapsAny b.1 b.2 (fr.filterMap (·.placedAt)))
  -- `PlanReq.optionalFold`, over `PlanReq.optionalFree` and `PlanReq.optionalOccupied`
  let opt := (r.optionalCands.foldl optionalStep
    (Look.freeIntervals (max r.now.sec r.dayStart) m.wd
      (m.pf.2 ++ fr.filterMap (·.placedAt) ++
        (m.cut.slots.zip fa.slotOf).filterMap
          (fun p => if p.2.isSome then some (p.1.start, p.1.stop) else none) ++ ekb), [])).2.reverse
  -- `PlanReq.restRows`, over `PlanReq.restTaken`
  let rest : List Seg := ((m.es.zip fa.slotOf).filter (fun p => p.2.isNone)).flatMap
    (fun p => (Look.freeIntervals p.1.2.start p.1.2.stop
        (opt.map (fun o => (o.start, o.stop)) ++ fr.filterMap (·.placedAt))).map (fun iv =>
      { start := iv.1, stop := iv.2, kind := .rest, energy := some p.1.1, item := none,
        inst := none, flags := SegFlags.none, planned := none, mult := none, note := none }))
  -- `dayRoutineSegs`: `routineRows` over the final routines, `PlanReq.routineHot` read off `m.ca`
  let routineSegs : List Seg := fr.flatMap (fun (q : Placed) =>
      (match q.placedAt with
       | none => []
       | some (a, b) =>
         [{ start := a, stop := b, kind := .routine, energy := r.routineEnergy q.inst.id,
            item := some q.inst.id, inst := q.inst.inst.map (fun k => (q.inst.id, k)),
            flags := { SegFlags.none with mandatory := q.inst.mandatory, deferred := q.deferred,
                                          hot := !r.isFurniture q.inst.id &&
                                            (m.ca.find? (fun o => o.out.cand.id == q.inst.id)).any
                                              (fun o => o.out.p == some 0) },
            planned := some q.inst.durMin, mult := none, note := none }] : List Seg)) ++
    r.eveningRows
  -- `reservationSegs` = `PlanReq.activeRow`
  let resSegs : List Seg := match m.ar with
    | none => []
    | some q =>
      [{ start := q.start, stop := q.stop, kind := .block, energy := none, item := some q.id,
         inst := none, flags := { SegFlags.none with current := true },
         planned := some q.leftMin, mult := r.candMult q.id, note := some (.runningLeft q.leftMin) }]
  -- `PlanReq.assignedRows`
  let assignedSegs : List Seg := (m.es.zip fa.slotOf).filterMap (fun p =>
    match p.2 with
    | Option.none => Option.none
    | some gi =>
      match fa.groups[gi]? with
      | Option.none => Option.none
      | some g => some (assignedSeg p.1.1 p.1.2 g))
  -- `PlanReq.keptBreakRows`
  let keptSegs : List Seg := ekb.map (fun b =>
    { start := b.1, stop := b.2, kind := .brk, energy := none, item := none, inst := none,
      flags := SegFlags.none, planned := some (Look.spanMinutes b.1 b.2), mult := none,
      note := none })
  -- `PlanReq.optionalRows`
  let optSegs : List Seg := opt.map (fun o =>
    { start := o.start, stop := o.stop, kind := .optional, energy := none, item := some o.id,
      inst := none, flags := SegFlags.none, planned := some o.want, mult := none,
      note := none })
  -- `dayRows`
  let rows := sortRows ((stepOneOrder r ++ resSegs ++ assignedSegs ++ keptSegs ++
    optSegs ++ rest ++ routineSegs).map segOf)
  -- `dayAssigned`
  let assigned := (rows.filter (fun s => s.val.kind.isWork)).flatMap segItems
  -- `PlanReq.dayImpossible`
  let imp := m.ca.filterMap (fun o =>
    if 0 < o.shortfall then
      some (o.out.cand.id, Arith.floorQ (Arith.mkPos o.shortfall Look.capDen Look.capDen_pos))
    else none)
  -- `PlanReq.restHighMin`
  let high := (rest.filter (fun s =>
      match s.energy with | some e => decide (4 ≤ e.val) | Option.none => false)).foldl
    (fun a s => a + s.minutes) 0
  { DayPlan.empty r.today m.win r.blockMin r.budgetBlocks with
    segments := rows
    diagnostics := { Diagnostics.empty with
      underused := Capped.ofListTake
        ((rows.filter (fun s => s.val.flags.underused && s.val.kind.isWork)).flatMap segItems)
      hot := Capped.ofListTake ((m.ca.filterMap (fun o =>
        if !o.out.cand.wall &&
            (decide (o.out.bin = some Arith.Bin.hot) || decide (o.cls = Look.PClass.hotFlag))
        then some o.out.cand.id else none)).eraseDups)
      impossible := Capped.ofListTake imp
      conflicts := Capped.ofListTake (wallConflicts (wallsToday r))
      blocked := Capped.ofListTake r.dayBlocked
      deferred := Capped.ofListTake
        (let both := m.es.zip
          (Look.energizeToday { r.look with today0 := { r.look.today0 with reports := [] } } m.cut.slots)
         (r.cands.val.filterMap (fun cf =>
          if !cf.1.wall && !assigned.contains cf.1.id && cf.1.plan.val.eligible && !cf.1.optional &&
              !cf.1.window &&
              both.any (fun p => decide (cf.1.ci ≤ p.2.1) && decide (p.1.1 < cf.1.ci))
          then some cf.1.id else none)).eraseDups)
      waiting := Capped.ofListTake r.dayWaiting
      aCapacityLost :=
        if (decide (0 < high) &&
            (r.cands.val.map Prod.fst).any (fun c =>
              decide (c.ci.val = 5) && !c.wall && !c.optional && !assigned.contains c.id)) = true
        then high else 0
      notes := Capped.ofListTake
        ((if travelDay r then [Note.travelDay] else []) ++
          fr.filterMap (fun q =>
            if q.placedAt.isSome then none
            else if q.span.2 ≤ max q.span.1 r.now.sec then none
            else some (Note.noPosition q.inst.id q.inst.durMin (max q.span.1 r.now.sec) q.span.2)) ++
          r.budgetSpentNotes)
      droppedTail := Capped.ofListTake
        (((m.groups.flatMap (fun g => g.members.map (fun x => x.cand.id))).filter
          (fun i => !assigned.contains i)).eraseDups)
      planHonesty :=
        (let budgetMin := m.bud * r.blockMin
         if budgetMin = 0 then (0, 0)
         else
           ((m.groups.filter (fun g =>
               g.members.any (fun x => assigned.contains x.cand.id))).foldl
                 (fun acc g => acc + g.commitMin) 0,
            budgetMin))
      restDebtMin := r.dayRestDebtMin
      impossibleUntil := Capped.ofListTake (m.ca.filterMap (fun o =>
        if 0 < o.shortfall then
          (answerUntil o).map (fun u =>
            (o.out.cand.id, Arith.floorQ (Arith.mkPos o.shortfall Look.capDen Look.capDen_pos), u))
        else none))
      underusedLevels := Capped.ofListTake
        ((rows.filter (fun s => s.val.flags.underused && s.val.kind.isWork)).flatMap
          (fun s => (segItems s).map (fun i => (i, s.val.energy.getD 0, r.candCi i))))
      blockedDeps := Capped.ofListTake r.dayBlockedDeps
      served := Capped.ofListTake
        (m.ranked.map (fun x => (x.key.ix, x.out.out.cand.id, x.out.out.cand.ci)))
      unplaced := Capped.ofListTake
        (let slotOf := fa.slotOf
         (imp.map Prod.fst).eraseDups.filterMap (fun i =>
          let xs := m.es.zipIdx.filter (fun x => m.sg.any (fun g =>
            decide (i ∈ g.ids) &&
              groupFitsAt m.loc m.wd m.cut.slots (List.replicate m.cut.slots.length Option.none)
                m.cut.breaks x.2 x.1.1 x.1.2 g))
          if assigned.contains i then none else if xs.isEmpty then some (i, .noSlotAdmits)
          else if xs.any (fun x => (slotOf[x.2]?).join.isNone) then some (i, .budgetSpent)
          else some (i, if m.sg.any (fun g => decide (i ∈ g.ids) && !g.splittable) then .noRunLeft
            else .noSlotLeft))) }
    priorities := m.pri
    planHash := planDigest r.tz (rows.map Subtype.val) }

/-- **The day, each view computed once**: the memo, then step 6 over it, then the rows and the
diagnostics over both. -/
def dayPlanOnce (r : PlanReq) : DayPlan :=
  let m := Memo.of r
  dayPlanFrom r m (walkDefer (deferOneAt r m) [] m.af m.pf.1.reverse)

/-- **`dayPlanFrom` over the views and step 6's own fold is `Planner.dayPlan`** — one `rfl`:
every binding of `dayPlanFrom` is the body of the view it names. -/
theorem dayPlanFrom_spec (r : PlanReq) : dayPlanFrom r (Memo.of r) r.deferFold = dayPlan r := rfl

/-- **The twin is the day**, on every request. -/
theorem dayPlanOnce_eq (r : PlanReq) : dayPlanOnce r = dayPlan r := by
  show dayPlanFrom r (Memo.of r)
      (walkDefer (deferOneAt r (Memo.of r)) [] (Memo.of r).af (Memo.of r).pf.1.reverse) = dayPlan r
  rw [walkDefer_eq r (remainingBudget r) _ (deferOneAt_eq r)]
  exact dayPlanFrom_spec r

/-- **The compiler runs the twin** wherever this module is imported (`PlanWire.lean`). -/
@[csimp] theorem dayPlan_eq_dayPlanOnce : @dayPlan = @dayPlanOnce := by
  funext r
  exact (dayPlanOnce_eq r).symm

end Planner
end Tm
