import TmKernel.Boundary
import TmKernel.PlanCheck
import TmKernel.Recur
/-!
# A `PlanReq` that can be written down, and the four witnesses it unblocks

Stage 6, track W (run W-15).  README **gap 348**: *"no `PlanReq` can be built inside
`Planner.lean`, so the wall laws have no end-to-end witness"* — and the W-14 repair step made
that gap the blocker for three others (366, 393's witness half, 396).  This module is gap 348
item 4's second option, taken by name: *"a small `PlannerWit.lean` importing `Boundary` and
`Planner`"*.  It imports `Boundary` for `loadPlan` and `PlanCheck` for the battery.

**What imports it, measured (W-17, track G).**  The sentence that stood here said *"nothing
imports it, so no shipped path grows"*, and the first clause is **false as written**:
`TmKernel/TmKernel.lean:82` carries `import TmKernel.PlannerWit`, put there in the same commit
that created this module (`3096320`) because AGENTS §9.2 lists *"a new module that is never
imported into `TmKernel/TmKernel.lean`"* among the disguised gaps — it would look built and
check 1 would agree.  `Check.lean`, `Negative.lean` and `Goals.lean` reach it from there
through `import TmKernel`, which is what puts its 64 audit lines under check 3 and its
`decide` witnesses under check 1.

What is true, and is what the sentence meant, is that **no library module imports it**:
`grep -l 'import TmKernel.PlannerWit' TmKernel/TmKernel/*.lean` is empty, so it is a leaf of
the import graph, `Boundary.lean` (the only module the FFI enters) cannot reach it, and no
shipped path grows.  **That is the right shape and it should stay that way**: this module
exists to *evaluate* the planner on concrete requests, so anything that imported it would be
importing 40 000-`maxRecDepth` witnesses into its own elaboration.  A module nothing imports
is weaker evidence than a driven verb (AGENTS §5.6) — and the honest reading of that rule here
is that these witnesses are evidence about the **kernel's own output**, not about the binary:
`dayPlan` has no shipped caller at all yet (README gap 501's sibling — there is no planner op
on the wire), so no witness in this file can be driven from `tm` until the wire carries one.

## Why a module and not a witness inside `Planner.lean`

A `PlanReq` needs a `WfPlan` and a `Seal.Run`.  The only `WfPlan` constructor is
`Boundary.loadPlan`'s and the only `Seal.Run` constructor is `Seal.resumeRun`'s, and neither
`Planner.lean` nor `PlanCheck.lean` imports `Boundary` — deliberately, so that track P and
track K cannot collide in the one file design §19 item 6 warns about.  Gap 348 item 4 says the
witness goes in a new module importing both, *"and it should be one of them and not both"*.

## The builder (`mkPlanReq?`), and what it is for

`mkPlanReq?` is a **decoder-shaped** assembler: it takes the raw parts a host has — the plan's
documents, the log's lines, the lookahead's raw input, the EDF denominator and §9's runtime
rows — and runs each through the constructor that already owns it:

| field | through | refuses |
|---|---|---|
| `plan` | `Boundary.loadPlan` | the loader's own `JVal` diagnostic |
| `look` | `Look.mkInput?` (L5) | `Look.CapErr`, by name |
| `run` | `Seal.resumeRun` from genesis (`Seal.Ckpt.empty`) | `Seal.Refusal`, by name |
| `caps` | `lookaheadOf?` | `caps` (a zero denominator, or days out of order) |
| the two agreeing | `PlanReq.wallsAgree` | `walls` |

**Nothing here re-implements any of them** (AGENTS §5.3): every line of `mkPlanReq?` is a call.
The one *new* obligation it discharges is the last row, and that is the point of it:
`mkPlanReq?_ok_wallsAgree` proves that **every request this builder accepts satisfies
`PlanReq.wallsAgree`**, which README gap 346 records as a hypothesis with no caller to
discharge it.  It still is not an invariant of the type — gap 346 stays open, because the
*wire* decoder is still unwritten — but it is now a theorem about a real constructor rather
than a promise about a hypothetical one.

## The witness, and the one rule its `decide`s obey

`theRequest` is the §4.3 Wednesday, 2026-09-09, in Chicago at 14:00: the boundary's own
one-line calendar (`Boundary.lookWallWitness`, the 12:50–13:50 meeting `^g1`) as the plan, a
six-line log for that morning as the run, and the shipped `[day]`, `[expected]` and `[energy]`
configuration as the lookahead input.  Everything it is built from is **reused**, not rewritten:
the plan is `Boundary.lookWallPlan`, the wall index equation is
`Boundary.the_look_wall_calendar_indexes_one_wednesday_wall`, the configuration is
`Look.DayCfg.shipped` / `Look.Curves.shipped` / `Look.shippedArrival` / `Look.specToday`.

**No `decide` holds two stages of the pipeline**, which is the practice `Boundary.lean`'s own
L5 witness states out loud (*"the plan is evaluated under `decide` once … so no `decide` holds
both the load and the lookahead"*).  `witBuilds` is proved by **rewriting** with the four
stage equations, never by deciding the builder end to end.

**And the log lines are spelled as characters, not as `"…".toList`.**  This is not a style
choice and it cost a measurement to learn: `Log.lineEntries` on ONE line written
`"{\"t\":…}".toList` exhausts a `MemoryMax=8G` probe in 12.6 s (exit 137), and the identical
line spelled `['{','"','t','"',…]` decides in **0.21 s**.  `Boundary.logWitnessLine`'s comment
— *"spelled as characters (the parser reads it)"* — is the same finding, undated; README gap
452 records it where the next agent will look.

## These `decide`s are build-time walls, and the steps that fill the day will break them

Every theorem below that names `dayPlan theRequest` is an equation about the day **step P1**
produces.  `PlanCheck.dayPlan_ok_core` was written the same way over step P0's empty day and
stopped compiling the moment P1 placed a row — which is how the W-14 merge found two findings
at merge time instead of at P5, and is AGENTS §3.1 item 1 taken rather than described.  The
same thing will happen here: **P2 (routines), P3 (slots) and P5 (assign) each add rows, and
each will make `the_witness_day_is_two_replayed_blocks_the_written_wall_and_the_evening`,
`the_witness_assigns_the_two_replayed_blocks`, `the_battery_passes_at_the_witness` and
`the_battery_bites_at_the_witness` fail to reduce.**  That is the intended cost: the step that
fills the day re-derives the four equations and the reader sees exactly what the new step put
in the day.  Re-deriving them is a `decide`, not a proof.

`the_witness_assigns_nothing_after_now` and
`the_budget_does_not_reach_the_assigned_set_until_the_assign_fold_lands` are different: they
are **tripwires P5 must delete**, beside
`Planner.the_day_assigns_nothing_after_now_but_the_running_block` (which step P3 restated from
`…_until_the_assign_step_lands`, because §8.2 choice 5b's reservation made the empty-list form
false).
-/

namespace Tm
namespace PlannerWit

open Planner

/-! ############################################################################
## 1. The builder
############################################################################ -/

/-- Why a request cannot be assembled, by name (AGENTS §5.7).  Each constructor carries the
refusal of the decoder that produced it, so a failure names the stage as well as the reason. -/
inductive WitErr
  /-- `Boundary.loadPlan` refused the documents. -/
  | plan (e : JVal)
  /-- `Look.mkInput?` refused the lookahead input (L5's `CapErr`). -/
  | input (e : Look.CapErr)
  /-- `Seal.resumeRun` refused the log (§9.3's guards). -/
  | run (e : Seal.Refusal)
  /-- **P4**: more candidates than `maxCands`.  The cap is `Capped`'s, which is the wire's own
  (`Boundary.maxCandidates`); this constructor only carries the refusal out. -/
  | cands
  /-- The wall index is not the plan's own (README gap 346). -/
  | walls
  /-- **P2's `mkRoutines?` refused a window instance** (W-15's land step).  The rule is
  `Planner.mkRoutine?`'s and only its; this constructor carries the refusal out, it does
  not restate it (AGENTS §5.3). -/
  | routines (e : RoutineErr)
deriving Repr

/-- The raw parts a host has before any of them is decoded. -/
structure PlanReqIn where
  /-- The plan's documents, as the wire sends them (`Boundary.ReqDoc`). -/
  docs      : List ReqDoc
  /-- `.tm/log.jsonl` from line 1: this builder resumes from genesis, never from a checkpoint,
  so the witness's run is the whole log and not a tail. -/
  lines     : List Log.Line
  /-- The lookahead's raw input (L5's `InputIn`): tz, `[day]`, curves, the weekday tables, the
  wall index and today's runtime facts. -/
  input     : Look.InputIn
  /-- §9's five rows `Look.Today` does not carry. -/
  state     : RuntimeIn
  /-- **§8.2 step 4's candidates, as the host sends them** (P4), each with its floor.  Uncapped
  here; `Capped.ofList?` is what caps them, exactly as the wire's `readCands` does. -/
  cands     : List (Look.Cand × Option Look.Floor)
  /-- §7's configuration (`capacity.priority` and `candidates.hysteresis`). -/
  prio      : PrioCfg
  /-- **§8.2 step 2's window instances, as the host sends them** (P2).  Uncapped and
  undecoded here; `Planner.mkRoutines?` is what caps and refuses them. -/
  routines  : List RoutineIn
  /-- §9.1's what-if overrides. -/
  overrides : Option PlanOverrides

/-- **The builder.**  Five decoders and one agreement check; nothing is re-implemented. -/
def mkPlanReq? (x : PlanReqIn) : Except WitErr PlanReq :=
  match loadPlan x.docs with
  | .error e => .error (.plan e)
  | .ok p =>
    match Look.mkInput? x.input with
    | .error e => .error (.input e)
    | .ok I =>
      if I.walls ≠ Look.wallIndex I.tz I.day.cut.blockMin p.val then .error .walls else
      match Seal.resumeRun I.tz I.today (Seal.Ckpt.empty I.tz) x.lines with
      | .error e => .error (.run e)
      | .ok run =>
        match Capped.ofList? x.cands with
        | none => .error .cands
        | some cs =>
          match mkRoutines? p.val x.routines with
          | .error e => .error (.routines e)
          | .ok rs => .ok ⟨p, run, I, x.state, cs, x.prio, rs, x.overrides⟩

/-! ### The rejection theorems (R10): every stage's refusal is reachable and named -/

theorem mkPlanReq?_refuses_a_plan_the_loader_refuses (x : PlanReqIn) (e : JVal)
    (h : loadPlan x.docs = .error e) : mkPlanReq? x = .error (.plan e) := by
  simp [mkPlanReq?, h]

theorem mkPlanReq?_refuses_an_input_the_decoder_refuses (x : PlanReqIn) (p : WfPlan)
    (e : Look.CapErr) (hp : loadPlan x.docs = .ok p)
    (h : Look.mkInput? x.input = .error e) : mkPlanReq? x = .error (.input e) := by
  simp [mkPlanReq?, hp, h]

/-- **README gap 346, from the other side**: a request whose wall index is not its own plan's
is refused by name rather than built and carried. -/
theorem mkPlanReq?_refuses_a_wall_index_that_is_not_the_plans (x : PlanReqIn) (p : WfPlan)
    (I : Look.Input) (hp : loadPlan x.docs = .ok p) (hI : Look.mkInput? x.input = .ok I)
    (h : I.walls ≠ Look.wallIndex I.tz I.day.cut.blockMin p.val) :
    mkPlanReq? x = .error .walls := by
  simp [mkPlanReq?, hp, hI, h]

theorem mkPlanReq?_refuses_a_run_the_guards_refuse (x : PlanReqIn) (p : WfPlan)
    (I : Look.Input) (e : Seal.Refusal) (hp : loadPlan x.docs = .ok p)
    (hI : Look.mkInput? x.input = .ok I)
    (hw : I.walls = Look.wallIndex I.tz I.day.cut.blockMin p.val)
    (h : Seal.resumeRun I.tz I.today (Seal.Ckpt.empty I.tz) x.lines = .error e) :
    mkPlanReq? x = .error (.run e) := by
  simp [mkPlanReq?, hp, hI, hw, h]

/-- **P4's R10 refusal**: a request that sends more than `maxCands` candidates is refused by
name rather than truncated.  (This replaced `mkPlanReq?_refuses_a_zero_denominator`, which the
EDF lookahead's promotion from a field to a view — `Planner.PlanReq.caps` — made unreachable:
`Look.lookahead_is_a_lookahead` proves `lookaheadOf?` cannot answer `none` for it.) -/
theorem mkPlanReq?_refuses_too_many_candidates (x : PlanReqIn) (p : WfPlan) (I : Look.Input)
    (run : Seal.Run) (hp : loadPlan x.docs = .ok p) (hI : Look.mkInput? x.input = .ok I)
    (hw : I.walls = Look.wallIndex I.tz I.day.cut.blockMin p.val)
    (hr : Seal.resumeRun I.tz I.today (Seal.Ckpt.empty I.tz) x.lines = .ok run)
    (h : maxCands < x.cands.length) : mkPlanReq? x = .error .cands := by
  simp [mkPlanReq?, hp, hI, hw, hr, Capped.ofList?_refuses_past_the_cap _ h]

/-- **The routine refusal is reachable and named** (R10, W-15's land step).  The rule is
`Planner.mkRoutine?`'s — this builder only carries its `RoutineErr` out under `WitErr.routines`,
so gap 285's refusal is not dropped between the wire and the request either. -/
theorem mkPlanReq?_refuses_a_routine_the_rule_refuses (x : PlanReqIn) (p : WfPlan)
    (I : Look.Input) (run : Seal.Run) (cs : Capped (Look.Cand × Option Look.Floor))
    (e : RoutineErr)
    (hp : loadPlan x.docs = .ok p) (hI : Look.mkInput? x.input = .ok I)
    (hw : I.walls = Look.wallIndex I.tz I.day.cut.blockMin p.val)
    (hr : Seal.resumeRun I.tz I.today (Seal.Ckpt.empty I.tz) x.lines = .ok run)
    (hcs : Capped.ofList? x.cands = some cs)
    (h : mkRoutines? p.val x.routines = .error e) :
    mkPlanReq? x = .error (.routines e) := by
  simp [mkPlanReq?, hp, hI, hw, hr, hcs, h]

/-! ### What every accepted request satisfies -/

/-- **Every request the builder accepts has `wallsAgree`.**  README gap 346 records
`PlanReq.wallsAgree` as *"a hypothesis, not an invariant"*, with *"no caller yet to discharge
it"*.  There is one now.  The gap does not close — the **wire** decoder is still unwritten, and
the type still does not forbid a disagreeing pair — but every law that carries `hagree` is
dischargeable at any request this builder made, and `theRequest_wallsAgree` below is the first
place that happens. -/
theorem mkPlanReq?_ok_wallsAgree (x : PlanReqIn) (r : PlanReq) (h : mkPlanReq? x = .ok r) :
    r.wallsAgree = true := by
  unfold mkPlanReq? at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  · rename_i hw
    split at h
    · cases h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        simp only [PlanReq.wallsAgree, PlanReq.tz, PlanReq.blockMin]
        exact decide_eq_true (Decidable.of_not_not hw)

/-- The parts come back out unchanged: the builder decodes, it does not adjust. -/
theorem mkPlanReq?_ok_parts (x : PlanReqIn) (r : PlanReq) (h : mkPlanReq? x = .ok r) :
    loadPlan x.docs = .ok r.plan ∧ Look.mkInput? x.input = .ok r.look ∧
      Seal.resumeRun r.look.tz r.look.today (Seal.Ckpt.empty r.look.tz) x.lines = .ok r.run ∧
      Capped.ofList? x.cands = some r.cands ∧ r.prio = x.prio ∧
      r.state = x.state ∧ mkRoutines? r.plan.val x.routines = .ok r.routines ∧
      r.overrides = x.overrides := by
  unfold mkPlanReq? at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · cases h
    · rename_i I hI
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i run hr
          split at h
          · cases h
          · rename_i la hla
            split at h
            · cases h
            · rename_i rs hrs
              cases h
              exact ⟨hp, hI, hr, hla, rfl, rfl, hrs, rfl⟩

/-! ############################################################################
## 2. The witness: the §4.3 Wednesday, built by the builder
############################################################################ -/

/-- §4.3's Wednesday at 14:00 local, on the shipped configuration: `Look.specToday` (nothing
stored in `state.json`, at the lounge, the home cap in force) with the day's own `now`. -/
def witToday : Look.Today :=
  { Look.specToday with now := ⟨(Cal.instantOf Cal.chicago 739867 840).sec, 0⟩ }

/-- The lookahead's raw input for that day: the shipped `[day]`, `[expected]` and curves, no
learned model, woken at 06:05, and the calendar's one wall. -/
def witInputIn : Look.InputIn where
  today := 739867
  days := 3
  today0 := witToday
  pModel := fun _ => none
  pConfig := fun
    | .friday => (8, 10) | .saturday => (5, 10) | .sunday => (4, 10) | _ => (9, 10)
  arrModel := fun _ => none
  arrConfig := Look.shippedArrival
  wake := some ⟨6 * 3600 + 5 * 60, 0⟩
  curves := Look.Curves.shipped
  homeMax := 3
  day := Look.DayCfg.shipped
  tz := Cal.chicago
  walls := Look.wednesdayWall

/-- `Boundary.loadsOk`'s shape for L5's decoder. -/
def inputOk (x : Look.InputIn) : Bool :=
  match Look.mkInput? x with | .ok _ => true | .error _ => false

set_option maxRecDepth 8000 in
theorem witInput_decodes_ok : inputOk witInputIn = true := by decide

/-- The decoded input.  Total by `witInput_decodes_ok`: the error branch is refuted, not
defaulted (`Boundary.lookWallPlan`'s pattern). -/
def witInput : Look.Input :=
  match h : Look.mkInput? witInputIn with
  | .ok I => I
  | .error _ => absurd witInput_decodes_ok (by simp [inputOk, h])

theorem witInput_decodes : Look.mkInput? witInputIn = .ok witInput := by
  unfold witInput
  split
  · rename_i I h; rw [h]
  · rename_i e h; exact absurd witInput_decodes_ok (by simp [inputOk, h])

theorem witInput_fields :
    witInput.today = 739867 ∧ witInput.tz = Cal.chicago ∧ witInput.day = Look.DayCfg.shipped ∧
      witInput.walls = Look.wednesdayWall ∧ witInput.today0 = witToday := by
  obtain ⟨-, -, -, -, ht, -, ht0, -, -, -, -, hd, hz, hw⟩ := Look.mkInput?_ok_elim witInput_decodes
  exact ⟨ht, hz, hd, hw, ht0⟩

/-- The plan loads, as an equation.  `Boundary.the_look_wall_witness_loads` is the `decide`;
this is the `.ok` form the builder rewrites with. -/
theorem lookWallPlan_loads : loadPlan lookWallWitness = .ok lookWallPlan := by
  unfold lookWallPlan
  split
  · rename_i p h; rw [h]
  · rename_i e h; exact absurd the_look_wall_witness_loads (by simp [loadsOk, h])

/-- **Six lines of `.tm/log.jsonl` for 2026-09-09**, in the fork's own bytes (the shapes are
`tm/tests/fixtures/fork-4748911-log-lines.jsonl`'s): woken 06:05 after 490 minutes, at the
lounge from 07:00 with a 07:00–15:00 window and a budget of 6, then two finished blocks —
`m1` 07:05–08:05 and `m2` 09:05–10:05.

**Spelled as characters on purpose** (module header): `"…".toList` on a line of this length
exhausts an 8 GiB probe inside `Log.lineEntries`; the character list decides in a fifth of a
second. -/
def witLines : List Log.Line :=
  [
  ⟨1, some
    ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','9','T','0','6',':','0','5',':','0','0','-','0','5',':','0','0','"',',','"','e','v','"',':','"','w','a','k','e','"',',','"','s','l','e','p','t','_','m','i','n','"',':','4','9','0','}']⟩,
  ⟨2, some
    ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','9','T','0','7',':','0','0',':','0','0','-','0','5',':','0','0','"',',','"','e','v','"',':','"','a','r','r','i','v','e','"',',','"','l','o','c','"',':','"','l','o','u','n','g','e','"',',','"','w','i','n','d','o','w','"',':','[','"','0','7',':','0','0','"',',','"','1','5',':','0','0','"',']',',','"','b','u','d','g','e','t','"',':','6','}']⟩,
  ⟨3, some
    ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','9','T','0','7',':','0','5',':','0','0','-','0','5',':','0','0','"',',','"','e','v','"',':','"','s','t','a','r','t','"',',','"','i','d','"',':','"','m','1','"',',','"','p','r','e','d','"',':','5',',','"','r','e','p','"',':','4',',','"','h','s','w','"',':','1','.','0',',','"','s','l','e','p','t','_','m','i','n','"',':','4','9','0',',','"','l','o','c','"',':','"','l','o','u','n','g','e','"',',','"','b','l','o','c','k','s','_','d','o','n','e','"',':','0',',','"','s','i','n','c','e','_','b','r','e','a','k','_','m','i','n','"',':','0','}']⟩,
  ⟨4, some
    ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','9','T','0','8',':','0','5',':','0','0','-','0','5',':','0','0','"',',','"','e','v','"',':','"','d','o','n','e','"',',','"','i','d','"',':','"','m','1','"',',','"','e','s','t','_','m','i','n','"',':','6','0',',','"','a','c','t','u','a','l','_','m','i','n','"',':','6','0',',','"','w','e','n','t','"',':','3',',','"','t','a','g','s','"',':','[',']',',','"','c','i','"',':','5','}']⟩,
  ⟨5, some
    ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','9','T','0','9',':','0','5',':','0','0','-','0','5',':','0','0','"',',','"','e','v','"',':','"','s','t','a','r','t','"',',','"','i','d','"',':','"','m','2','"',',','"','p','r','e','d','"',':','5',',','"','r','e','p','"',':','4',',','"','h','s','w','"',':','3','.','0',',','"','s','l','e','p','t','_','m','i','n','"',':','4','9','0',',','"','l','o','c','"',':','"','l','o','u','n','g','e','"',',','"','b','l','o','c','k','s','_','d','o','n','e','"',':','1',',','"','s','i','n','c','e','_','b','r','e','a','k','_','m','i','n','"',':','6','0','}']⟩,
  ⟨6, some
    ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','9','T','1','0',':','0','5',':','0','0','-','0','5',':','0','0','"',',','"','e','v','"',':','"','d','o','n','e','"',',','"','i','d','"',':','"','m','2','"',',','"','e','s','t','_','m','i','n','"',':','6','0',',','"','a','c','t','u','a','l','_','m','i','n','"',':','6','0',',','"','w','e','n','t','"',':','3',',','"','t','a','g','s','"',':','[',']',',','"','c','i','"',':','4','}']⟩
]

/-- `loadsOk`'s shape for the resume. -/
def runOk (z : Cal.Tz) (T : Nat) (ls : List Log.Line) : Bool :=
  match Seal.resumeRun z T (Seal.Ckpt.empty z) ls with | .ok _ => true | .error _ => false

set_option maxRecDepth 40000 in
theorem witRun_resumes_ok : runOk Cal.chicago 739867 witLines = true := by decide

def witRun : Seal.Run :=
  match h : Seal.resumeRun Cal.chicago 739867 (Seal.Ckpt.empty Cal.chicago) witLines with
  | .ok run => run
  | .error _ => absurd witRun_resumes_ok (by simp [runOk, h])

theorem witRun_resumes :
    Seal.resumeRun Cal.chicago 739867 (Seal.Ckpt.empty Cal.chicago) witLines = .ok witRun := by
  unfold witRun
  split
  · rename_i run h; rw [h]
  · rename_i e h; exact absurd witRun_resumes_ok (by simp [runOk, h])

/-- §7's configuration for the witnesses: §16's default bin ladder, R1's 1.3 safety factor,
`default_priority = 3` and §7.4's hysteresis on — the four `Look.priorities_on_a_witness` is
computed at, so the answers below are stage 5's answers and not a second set.

*(`witCaps`, `witCaps_ok` and `witCaps_eq` stood here until step P4 and are **deleted**: the EDF
lookahead stopped being a field of `PlanReq` and became `Planner.PlanReq.caps`, a view of
`Look.lookahead r.look`, so a request no longer carries one to build.  `Check.lean`'s P4 banner
records both deletions.)* -/
def witPrio : PrioCfg := ⟨Look.defaultBinsV, Arith.safety, specDefaultPrio, true, 20⟩

/-- The raw request. -/
def witReqIn : PlanReqIn where
  docs := lookWallWitness
  lines := witLines
  input := witInputIn
  state := RuntimeIn.empty
  cands := []
  prio := witPrio
  routines := []
  overrides := none

/-- **The request `Planner.lean` could not write down** (README gap 348).  Its routine list
is EMPTY: the witness day is two replayed blocks and the written wall, and P2's placement
adds no row to a day whose host sent no window instance
(`the_witness_carries_no_routine`). -/
def theRequest : PlanReq :=
  ⟨lookWallPlan, witRun, witInput, RuntimeIn.empty, Capped.nil, witPrio, Capped.nil, none⟩

/-- **The builder accepts it**, by rewriting with the four stage equations — never by a
`decide` that holds the load, the resume and the lookahead at once. -/
theorem witBuilds : mkPlanReq? witReqIn = .ok theRequest := by
  obtain ⟨ht, hz, hd, hw, -⟩ := witInput_fields
  unfold mkPlanReq? witReqIn theRequest
  simp only [lookWallPlan_loads, witInput_decodes]
  rw [if_neg (by
    rw [hw, hz, hd]
    simp only [Look.DayCfg.shipped, Look.CutCfg.shipped, ne_eq]
    exact not_not_intro the_look_wall_calendar_indexes_one_wednesday_wall.symm)]
  rw [hz, ht, witRun_resumes]
  simp only [Capped.ofList?_nil, mkRoutines?_of_none]

/-- **`hagree` is discharged for this request** — the hypothesis README gap 346 says has no
caller, and the hypothesis `PlanCheck.dayPlan_ok_core` and `Planner.plan_never_moves_a_wall`
both carry. -/
theorem theRequest_wallsAgree : theRequest.wallsAgree = true :=
  mkPlanReq?_ok_wallsAgree witReqIn theRequest witBuilds

/-! ############################################################################
## 3. What the day actually is, computed
############################################################################ -/

set_option maxRecDepth 40000 in
/-- **The day, end to end**: two Block rows replayed from the morning's log, one Wall row placed
from the calendar's own `at:`, and §16's two evening rows, in the fork's row order.  Every
endpoint is written here as `Cal.instantOf` of a local clock, so the equation is readable and is
about the same instants the plan and the log are written in.

This is the theorem README gap 348 says does not exist — *"there is no witness that says 'here
is a request whose `dayPlan` contains this row'"*.

**RE-PROVED AT W-15'S LAND STEP, and renamed with it.**  Track W wrote this against
`d2c0aa6`, where the day ended at the wall; track P's P2 landed §16's `wind_down` and `bed`
in the same run, so the day this request plans really is five rows, and the three-row form
this theorem had is FALSE — `decide` says so, which is how the merge found it.  Nothing was
downgraded or deleted (D5, AGENTS §3.1 item 3): the equation is re-proved over P2's day and
the name now says what it states (§5.2).  The two new rows carry `none` for their item,
which is what makes `assignedOf` still empty below.  The last endpoint is written as the
NEXT day's midnight (`739868`, minute 0) and not as minute 1440 of this one, because
`Cal.instantOf` takes a minute *of* the day and wraps 1440 back to 00:00 — writing it the
tempting way would have made the equation say the sleep row ends before it starts. -/
theorem the_witness_day_is_two_replayed_blocks_the_written_wall_and_the_evening :
    (dayPlan theRequest).segments.map (fun s => (s.val.start, s.val.stop, s.val.kind, s.val.item))
      = [((Cal.instantOf Cal.chicago 739867 425).sec, (Cal.instantOf Cal.chicago 739867 485).sec,
          SegKind.block, some (['m','1'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 545).sec, (Cal.instantOf Cal.chicago 739867 605).sec,
          SegKind.block, some (['m','2'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 770).sec, (Cal.instantOf Cal.chicago 739867 830).sec,
          SegKind.wall, some (['g','1'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 1290).sec, (Cal.instantOf Cal.chicago 739867 1320).sec,
          SegKind.windDown, none),
         ((Cal.instantOf Cal.chicago 739867 1320).sec, (Cal.instantOf Cal.chicago 739868 0).sec,
          SegKind.sleep, none)] := by
  decide

/-- **The witness sends no window instance**, which is why P2's placement fold adds no row of
its own to the day above: the two evening rows are §16's, not a routine's. -/
theorem the_witness_carries_no_routine : theRequest.routines.val = [] := rfl

set_option maxRecDepth 40000 in
/-- The day's window, budget and block length, computed through `Look.day0Window` and
`Look.budgetOf` — never through a second copy (`PlanReq.window_is_the_lookaheads`). -/
theorem the_witness_day_is_planned_from_two_in_the_afternoon :
    (dayPlan theRequest).window
        = ((Cal.instantOf Cal.chicago 739867 840).sec, (Cal.instantOf Cal.chicago 739867 1140).sec) ∧
      (dayPlan theRequest).budgetBlocks = 6 ∧ (dayPlan theRequest).blockMin = 60 := by
  decide

/-! ############################################################################
## 4. README gap 393's witness half: a replayed Block really is assigned
############################################################################ -/

set_option maxRecDepth 40000 in
/-- **`assignedOf (dayPlan r) = []` is not a law of this planner, and here is the `r`.**

The W-14 repair proved `PlanCheck.a_replayed_block_is_assigned` — *"a Block the log holds for
today is work, is a row of the day, and its items are in `assignedOf`"* — and said in its own
doc comment that the claim it replaced had been justified by a theorem P1 deleted.  What it
could not do was exhibit a request where the conclusion fires, because no `PlanReq` could be
written down (gap 348).  This is that request: the morning's two blocks, replayed through
D24's seam, are the day's assigned set. -/
theorem the_witness_assigns_the_two_replayed_blocks :
    assignedOf (dayPlan theRequest) = [['m','1'], ['m','2']] := by
  decide

set_option maxRecDepth 40000 in
/-- **And the set §8.3's laws are about is still empty**, at the same request — because
**nothing is running at it**.  `Planner.the_day_assigns_nothing_after_now_but_the_running_block`
is proved for every request; this is it fired at one whose `RuntimeIn` is empty, and it is the
tripwire P5 must delete.  `the_reserved_day_assigns_the_running_block` below is the same
computation at a request with a block running, where the set holds exactly that block.  The two
theorems together are the distinction the W-14 repair drew: `assignedOf` counts the replayed
past, `assignedFrom … now` counts the planner's own placements. -/
theorem the_witness_assigns_nothing_after_now :
    assignedFrom (dayPlan theRequest) theRequest.now.sec = [] := by
  decide

/-! ############################################################################
## 5. README gap 396: the battery, as a second opinion at a concrete request
############################################################################ -/

set_option maxRecDepth 40000 in
/-- **The battery passes at a request whose day has real Block rows**, computed.

README gap 396: *"`PlanCheck` gives no independent opinion on wall placement …
`dayPlan_ok_core`'s seventh check is `plan_never_moves_a_wall` applied through
`wallsUnmoved_iff`; the other six are vacuous under `hnopast`."*  Both halves are answered
here, and neither is answered by a second copy of a placement rule (which the W-14 land step
refused, AGENTS §5.3):

* the six block-side checks are **not vacuous** at this request — `hnopast` is false of it,
  because the log holds two Blocks (`the_witness_day_is_two_replayed_blocks_the_written_wall_and_the_evening`),
  so `dayPlan_ok_core` does not apply and this is not a restatement of it;
* the seventh, `wallsUnmoved`, recomputes **both** wall endpoints from the plan's own `at:`
  through `Cal.instantOf` and compares them with the row the planner placed.  Nothing in this
  proof mentions `Planner.plan_never_moves_a_wall`; it is the evaluator's answer, so a change
  to `Planner.wallRows` that moved a row would make this `decide` fail to reduce to `true` and
  `check.sh` check 1 would fail **in this module**. -/
theorem the_battery_passes_at_the_witness :
    PlanCheck.planOkCore theRequest (dayPlan theRequest) = true := by
  decide

set_option maxRecDepth 40000 in
/-- The clause that makes the theorem above a second opinion rather than a restatement:
`PlanCheck.dayPlan_ok_core`'s `hnopast` is **false** at this request, so the lift it proves is
not available here and nothing above was borrowed from it. -/
theorem the_witness_replays_a_block :
    (pastRows theRequest).any (fun t => t.kind == SegKind.block) = true := by
  decide

theorem the_witness_defeats_the_lifts_hypothesis :
    ¬ (∀ t ∈ pastRows theRequest, t.kind ≠ SegKind.block) := by
  intro h
  have hb := the_witness_replays_a_block
  simp only [List.any_eq_true, beq_iff_eq] at hb
  obtain ⟨t, ht, hk⟩ := hb
  exact h t ht hk

/-! ### It bites: three mutations of the day this request produced, each refused

A checker that answers `true` on the one day anyone ever hands it is AGENTS §9.2's *"check no
input can fail"*.  `PlanCheck`'s own `*_can_fail` witnesses answer that in general; these
answer it **at this request**, over the day the planner actually built, with the real store and
the real zone behind `effectiveCi` and `Cal.instantOf`. -/

/-- The day with the Wall row pushed one minute later than the calendar says. -/
def moveWallLater (s : WfSeg) : WfSeg :=
  if s.val.kind = SegKind.wall then Planner.segOf { s.val with start := s.val.start + 60 } else s

def theMovedWallDay : DayPlan :=
  { dayPlan theRequest with segments := (dayPlan theRequest).segments.map moveWallLater }

/-- The day with the first replayed Block laid across the meeting. -/
def ontoTheWall (s : WfSeg) : WfSeg :=
  if s.val.item = some (['m','1'] : Id) then
    Planner.segOf
      { s.val with
        start := (Cal.instantOf Cal.chicago 739867 780).sec
        stop := (Cal.instantOf Cal.chicago 739867 800).sec }
  else s

def theClashingDay : DayPlan :=
  { dayPlan theRequest with segments := (dayPlan theRequest).segments.map ontoTheWall }

/-- The day with the first replayed Block stretched to two hours. -/
def stretchIt (s : WfSeg) : WfSeg :=
  if s.val.item = some (['m','1'] : Id) then Planner.segOf { s.val with stop := s.val.stop + 3600 }
  else s

def theOverlongDay : DayPlan :=
  { dayPlan theRequest with segments := (dayPlan theRequest).segments.map stretchIt }

set_option maxRecDepth 40000 in
theorem the_battery_bites_at_the_witness :
    PlanCheck.wallsUnmoved theRequest theMovedWallDay = false ∧
      PlanCheck.noBlockOverAWall theRequest theClashingDay = false ∧
      PlanCheck.oneBlockAtATime theRequest theOverlongDay = false ∧
      PlanCheck.planOkCore theRequest theMovedWallDay = false ∧
      PlanCheck.planOkCore theRequest theClashingDay = false ∧
      PlanCheck.planOkCore theRequest theOverlongDay = false := by
  decide

/-! ############################################################################
## 6. README gap 366 / D29: what a builder does and does not buy for `plan_tail_drop`
############################################################################

**Re-derived from the code as it stands, not inherited.**  Gap 366's recorded reason was
corrected once already (gap 393) and the brief for this run says to derive it again with a
builder in hand.  Here is what the derivation finds.

1. **§8.2 choice 5b's witness is still not writable, and the builder does not change that.**
   D29's refutation is supposed to exhibit *"the running block reserved before the budget is
   consulted, so shrinking the budget drops items ranking ahead of the Active item while it
   stays"*.  There is no reservation and no budget consumption in `Planner.dayPlan` today:
   step P1 places walls, the running interruption and the replayed past, and
   `the_budget_does_not_reach_the_assigned_set_until_the_assign_fold_lands` below **proves**
   that the budget cannot reach `assignedOf` at all.  So the counterexample D29 names needs
   **P5**, not a witness.  Gap 366 item 4 already said "after P5 *and* after the builder";
   what is new here is that the first conjunct is now a theorem rather than a reading.
2. **The law as stage 6 wrote it is nevertheless FALSE, for a reason nobody had recorded**,
   and the builder makes the witness writable.  Its hypotheses pin `plan`, `now`, `window`,
   `blockMin` and the budget ordering — five *views* of a six-field record — and leave `run`
   free.  Since §8.2 step 1 replays the day's past half out of `PlanReq.run` (D24's seam),
   two requests that satisfy every hypothesis can disagree about the whole assigned set.
3. **D29's restatement inherits the hole.**  Erasing the Active item repairs the prefix
   failure choice 5b causes; it does not repair this one, and
   `erasing_the_active_item_does_not_repair_a_law_whose_run_is_free` says so for **every**
   choice of erased item.  A restatement shipped as written would be a `sorry` that cannot
   close, so `plan_tail_drop` is left in `Goals.lean` (AGENTS §3.1 item 3: a restatement
   without its refutation is a weakening) and the owner is owed one more hypothesis —
   `r'.run = r.run`, or the whole law stated over one run — before D29 can be discharged.

`PlanCheck.a_kept_reservation_defeats_the_prefix_but_not_the_erasure` remains the arithmetic
of choice 5b, proved at W-14 with the planner factored out.  Nothing here supersedes it. -/

/-- The same request with an empty log: the plan, the configuration and the walls of
`theRequest`, and nothing replayed. -/
def witReqIn0 : PlanReqIn := { witReqIn with lines := [] }

set_option maxRecDepth 40000 in
theorem witRun0_resumes_ok : runOk Cal.chicago 739867 [] = true := by decide

def witRun0 : Seal.Run :=
  match h : Seal.resumeRun Cal.chicago 739867 (Seal.Ckpt.empty Cal.chicago) [] with
  | .ok run => run
  | .error _ => absurd witRun0_resumes_ok (by simp [runOk, h])

theorem witRun0_resumes :
    Seal.resumeRun Cal.chicago 739867 (Seal.Ckpt.empty Cal.chicago) [] = .ok witRun0 := by
  unfold witRun0
  split
  · rename_i run h; rw [h]
  · rename_i e h; exact absurd witRun0_resumes_ok (by simp [runOk, h])

/-- **The same day, with nothing in the log.** -/
def theQuietRequest : PlanReq :=
  ⟨lookWallPlan, witRun0, witInput, RuntimeIn.empty, Capped.nil, witPrio, Capped.nil, none⟩

theorem witBuilds0 : mkPlanReq? witReqIn0 = .ok theQuietRequest := by
  obtain ⟨ht, hz, hd, hw, -⟩ := witInput_fields
  unfold mkPlanReq? witReqIn0 witReqIn theQuietRequest
  simp only [lookWallPlan_loads, witInput_decodes]
  rw [if_neg (by
    rw [hw, hz, hd]
    simp only [Look.DayCfg.shipped, Look.CutCfg.shipped, ne_eq]
    exact not_not_intro the_look_wall_calendar_indexes_one_wednesday_wall.symm)]
  rw [hz, ht, witRun0_resumes]
  simp only [Capped.ofList?_nil, mkRoutines?_of_none]

set_option maxRecDepth 40000 in
theorem the_quiet_day_assigns_nothing : assignedOf (dayPlan theQuietRequest) = [] := by
  decide

set_option maxRecDepth 8000 in
/-- **The budget cannot reach the assigned set**, for every request, because there is no assign
fold to spend it.  This is the half of README gap 366 the builder settles: §8.2 choice 5b's
counterexample compares `plan(budget)` with `plan(budget − Δ)`, and today those two are the
same list whatever Δ is.  The theorem is stated over `state.budget`, which is the one input
`PlanReq.budgetBlocks` reads besides the `[day]` formula
(`Planner.PlanReq.budget_is_the_stored_one_when_there_is_one`).

**P5 must delete this**, exactly as it must delete
`Planner.the_day_assigns_nothing_after_now_but_the_running_block`: the day the fold spends
the budget this stops being true, and the commit that breaks it is the commit that can write
D29's witness.

**RE-PROVED AT W-15'S LAND STEP (D5).**  Track W proved it by `rfl` against `d2c0aa6`, where
`dayRows` was step one alone.  Track P's P2 added step two in the same run, and one link in
that chain — `Planner.splitSleep` — takes the whole `PlanReq` and recurses, so two requests
that agree on every field a step-two row reads are no longer *definitionally* equal.  The
statement is unchanged and the quantifier is unchanged; what carries it now is
`Planner.splitSleep_congr` plus the fact that every other step-two link (`routineInstances`,
`bedSec`, `blockedByWalls`, `night`, `placeStep`, `routineRow`) still reduces on its own,
which is why the rest of the proof is still `rfl`. -/
theorem the_budget_does_not_reach_the_assigned_set_until_the_assign_fold_lands
    (r : PlanReq) (b : Option Nat) :
    assignedOf (dayPlan { r with
        look := { r.look with today0 := { r.look.today0 with budget := b } } })
      = assignedOf (dayPlan r) := by
  rw [assignedOf_dayPlan_drops_the_routine_rows, assignedOf_dayPlan_drops_the_routine_rows]
  rfl

set_option maxRecDepth 40000 in
/-- **`plan_tail_drop` as stage 6 wrote it is REFUTED** (AGENTS §3.1 item 3, D5) — and not by
§8.2 choice 5b, which is not reachable until P5 (see this section's header and
`the_budget_does_not_reach_the_assigned_set_until_the_assign_fold_lands`).

The witness is two requests built by `mkPlanReq?` that differ in **one field, `run`**, and
satisfy every hypothesis the goal states: the same plan, the same `now`, the same window, the
same block length and the same budget.  One replays a morning with two finished blocks and the
other replays an empty log, so `assignedOf` is `[m1, m2]` on one side and `[]` on the other,
and `[m1, m2]` is no prefix of `[]`.

The goal's hypotheses name five *views* of `PlanReq` and leave `run`, `caps`, `state` and
`overrides` free; since D24's seam put the day's past half inside `PlanReq.run`, the run is the
field the conclusion depends on most. -/
theorem plan_tail_drop_as_stage_6_wrote_it_is_refuted_by_the_run_it_does_not_pin :
    ¬ (∀ (r r' : PlanReq), r'.plan = r.plan → r'.now = r.now → r'.window = r.window →
        r'.blockMin = r.blockMin → r'.budgetBlocks ≤ r.budgetBlocks →
        ∃ n : Nat, assignedOf (dayPlan r') = (assignedOf (dayPlan r)).take n) := by
  intro h
  obtain ⟨n, hn⟩ :=
    h theQuietRequest theRequest rfl rfl rfl rfl (Nat.le_refl _)
  rw [the_witness_assigns_the_two_replayed_blocks, the_quiet_day_assigns_nothing,
    List.take_nil] at hn
  exact absurd hn (by simp)

/-- **D29's restatement does not repair it** — for **any** erased item, not merely for the
wrong one.  Erasing removes at most one element, and the two assigned sets here differ by two,
so `(assignedOf (dayPlan r')).erase a = ((assignedOf (dayPlan r)).erase a).take n` fails at the
same pair whatever `a` is — the Active item included, and there is no Active item in either
request to privilege.

This is the finding the owner is owed before D29 can be discharged: the Active erasure is the
right repair for choice 5b's prefix failure and is **not** a repair for an unpinned run. -/
theorem erasing_the_active_item_does_not_repair_a_law_whose_run_is_free (a : Id) :
    ¬ ∃ n : Nat, (assignedOf (dayPlan theRequest)).erase a
        = ((assignedOf (dayPlan theQuietRequest)).erase a).take n := by
  rintro ⟨n, hn⟩
  rw [the_witness_assigns_the_two_replayed_blocks, the_quiet_day_assigns_nothing] at hn
  simp only [List.erase_nil, List.take_nil] at hn
  -- `l.erase a = []` forces `l = []` or `l = [a]`, and the assigned set has two members.
  exact absurd hn (by simp)


/-! ## The recurrence, on a loaded routine (stage 6, step K3b)

`Recur.lean` has no shipped caller and no `Boundary` import, so its end-to-end
witnesses live here, in the module gap 348 built for exactly this: a `WfPlan`
needs `loadPlan` and a `Replay.Facts` needs the replay, and `Recur.lean` can
reach neither.

The line is §4.3's own `routines.md` lunch — a bare, box-less, id-less line, so
it is an entity only since K3a (D31) and its store key is its **title**.  The
day is the same Wednesday 2026-09-09 the request above plans. -/

/-- §4.3's `routines.md`, one line. -/
def recurWitness : List ReqDoc :=
  [⟨"routines.md", none, ["- lunch win:11:30-13:30 dur:30m every:day".toList]⟩]

set_option maxRecDepth 40000 in
theorem the_recur_witness_loads : loadsOk recurWitness = true := by decide

/-- The loaded routine.  Total by `the_recur_witness_loads`. -/
def recurPlan : WfPlan :=
  match h : loadPlan recurWitness with
  | .ok p => p
  | .error _ => absurd the_recur_witness_loads (by simp [loadsOk, h])

/-- A log with nothing in it: the facts a first day has. -/
def emptyFacts : Replay.Facts := Replay.replay Cal.chicago []

/-- 2026-09-09, the witness day. -/
def recurDay : Nat := 739867

theorem recurDay_is_the_witness_wednesday : recurDay = Cal.toDay ⟨2026, 9, 9⟩ := by decide

set_option maxRecDepth 100000 in
/-- **The lunch routine is today's occurrence, and at noon it is MANDATORY** —
§5.2's rule, end to end from the bytes: the window is 11:30 to 13:30 local, the
due point is its close, the status is `pending`, and `place_minutes` is the
line's own `dur:30m`.  This is the answer `Look.Cand`'s `due`, `window` and
`mandatory` are taken from the host for today (README gap 113). -/
theorem the_lunch_routine_is_todays_mandatory_window_at_noon :
    (Recur.todayInstanceOf 60 Cal.chicago recurPlan.val emptyFacts "lunch".toList recurDay
        (Recur.atClock recurDay ⟨720, by omega⟩)).map
      (fun x => (x.1.window, x.1.due, x.1.status)) =
      some (some (Recur.atClock recurDay ⟨690, by omega⟩, Recur.atClock recurDay ⟨810, by omega⟩),
            some (Recur.atClock recurDay ⟨810, by omega⟩), Log.InstanceStatus.pending) ∧
    (Recur.todayInstanceOf 60 Cal.chicago recurPlan.val emptyFacts "lunch".toList recurDay
        (Recur.atClock recurDay ⟨720, by omega⟩)).map
      (fun x => (x.2.mandatory, x.2.overdue, x.2.durMin)) = some (true, false, some 30) := by
  refine ⟨by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- **And at two in the afternoon there is no occurrence at all** — the expire
veto.  `on-miss:` defaults to `expire` on a `win:` shape (`defaultOnMiss`), the
window closed at 13:30, and `today_instances`' own filter
(`item.on_miss == Persist || close_of(i) >= now`) drops it: a chance that ran
out this morning is over, not a last chance and not a carry.  Sixty days of
earlier occurrences are `Expired` by §5.3 and are not actionable, so nothing is
carried either. -/
theorem the_lunch_routine_is_gone_by_two_in_the_afternoon :
    Recur.todayInstanceOf 60 Cal.chicago recurPlan.val emptyFacts "lunch".toList recurDay
        (Recur.atClock recurDay ⟨840, by omega⟩) = none := by
  decide

set_option maxRecDepth 100000 in
/-- **A carried `persist` routine is today's obligation, overdue, with the date
it was carried from** — §5.3's laundry, the half `every:day` + `on-miss:persist`
produces.  At 14:00 the window has closed, but `persist` keeps the instance and
`today_instances` reports **one** occurrence and not sixty-one. -/
def persistWitness : List ReqDoc :=
  [⟨"routines.md", none,
     ["- laundry win:11:30-13:30 dur:30m every:day on-miss:persist".toList]⟩]

set_option maxRecDepth 40000 in
theorem the_persist_witness_loads : loadsOk persistWitness = true := by decide

def persistPlan : WfPlan :=
  match h : loadPlan persistWitness with
  | .ok p => p
  | .error _ => absurd the_persist_witness_loads (by simp [loadsOk, h])

set_option maxRecDepth 100000 in
theorem a_persist_routine_is_one_carried_obligation_not_sixty_one :
    (Recur.todayInstances 60 Cal.chicago persistPlan.val emptyFacts ["laundry".toList] recurDay
        (Recur.atClock recurDay ⟨840, by omega⟩)).length = 1 := by
  decide

/-! ############################################################################
## 7. A request with a block running: §8.2 choice 5b, computed (stage 6, step P3)

The `theRequest` above has an empty `RuntimeIn`, so `Planner.PlanReq.activeRun` answers `none`
at it and every row of its day is step 1's or step 2's.  This section builds the *same* day
with a block running, which is the first request in the stage whose `dayPlan` holds a
`SegKind.block` row **the planner placed**, and computes what the battery says about it.

Why it matters, in one line each:

* it is the non-vacuity witness for `Planner.plan_reserves_one_block_at_a_time` and for
  `Planner.the_day_assigns_nothing_after_now_but_the_running_block` — without it both are
  statements about an empty set (AGENTS §5.2);
* it makes six of `PlanCheck`'s seven eligibility-free checks bite on a row the planner placed,
  where `PlanCheck.dayPlan_ok_core` used to discharge them under `hnopast` alone (README gap
  **396**, the half W-14 left open);
* the reservation it computes is **clipped by `current_block_end`** — 70 minutes are still
  owed and the row is 40 — which is the fork rule E1 turns on, run rather than argued.
############################################################################ -/

/-- §9's `state.active`: `m1` started at 13:40 with a 90-minute estimate, timer running.  The
id is the one the morning's log holds; the *plan* holds only the calendar's `g1`, which is why
the replayed rows above name items the store does not — the fork does the same. -/
def theRunningBlock : ActiveBlock :=
  ⟨['m','1'], ⟨(Cal.instantOf Cal.chicago 739867 820).sec, 0⟩, 90, false⟩

def theRunningState : RuntimeIn := { RuntimeIn.empty with active := some theRunningBlock }

def witReqInRun : PlanReqIn := { witReqIn with state := theRunningState }

/-- The §4.3 Wednesday at 14:00 with `m1` running. -/
def theRunningRequest : PlanReq :=
  ⟨lookWallPlan, witRun, witInput, theRunningState, Capped.nil, witPrio, Capped.nil, none⟩

theorem witBuildsRun : mkPlanReq? witReqInRun = .ok theRunningRequest := by
  obtain ⟨ht, hz, hd, hw, -⟩ := witInput_fields
  unfold mkPlanReq? witReqInRun witReqIn theRunningRequest
  simp only [lookWallPlan_loads, witInput_decodes]
  rw [if_neg (by
    rw [hw, hz, hd]
    simp only [Look.DayCfg.shipped, Look.CutCfg.shipped, ne_eq]
    exact not_not_intro the_look_wall_calendar_indexes_one_wednesday_wall.symm)]
  rw [hz, ht, witRun_resumes]
  simp only [Capped.ofList?_nil, mkRoutines?_of_none]

/-- **The request agrees with `mkActive?` and with `mkDayCfg?`** — the two R10 hypotheses
`Planner.plan_reserves_one_block_at_a_time` and `PlanCheck.dayPlan_ok_core` carry, discharged
at a request the builder accepts (README gap 346's shape). -/
theorem the_running_request_agrees :
    theRunningRequest.activeAgrees = true ∧ theRunningRequest.dayAgrees = true := by decide

set_option maxRecDepth 40000 in
/-- **The reservation, computed**: from `now` to the end of the `block_min` block it is in.
Seventy minutes are still owed (`leftMin = 70`, the estimate less the twenty worked since
13:40) and the row runs **forty** — `Planner.PlanReq.currentBlockEnd` is what cuts it, which is
the fork rule §8.3's E1 turns on.  Neither the estimate nor the window is what binds here, and
that is the point of computing it. -/
theorem the_reservation_is_clipped_to_the_block_it_is_in :
    theRunningRequest.activeRun.map (fun q => (q.start, q.stop, q.leftMin))
      = some ((Cal.instantOf Cal.chicago 739867 840).sec,
              (Cal.instantOf Cal.chicago 739867 880).sec, 70) := by
  decide

set_option maxRecDepth 40000 in
/-- **The day, end to end, with a block running**: the two replayed Blocks, the written wall,
**the reservation**, and §16's two evening rows — six rows, in the fork's row order. -/
theorem the_reserved_day_is_the_witness_day_and_the_running_block :
    (dayPlan theRunningRequest).segments.map (fun s => (s.val.start, s.val.stop, s.val.kind, s.val.item))
      = [((Cal.instantOf Cal.chicago 739867 425).sec, (Cal.instantOf Cal.chicago 739867 485).sec,
          SegKind.block, some (['m','1'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 545).sec, (Cal.instantOf Cal.chicago 739867 605).sec,
          SegKind.block, some (['m','2'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 770).sec, (Cal.instantOf Cal.chicago 739867 830).sec,
          SegKind.wall, some (['g','1'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 840).sec, (Cal.instantOf Cal.chicago 739867 880).sec,
          SegKind.block, some (['m','1'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 1290).sec, (Cal.instantOf Cal.chicago 739867 1320).sec,
          SegKind.windDown, none),
         ((Cal.instantOf Cal.chicago 739867 1320).sec, (Cal.instantOf Cal.chicago 739868 0).sec,
          SegKind.sleep, none)] := by
  decide

set_option maxRecDepth 40000 in
/-- **The reservation carries no slot energy and is marked `▶`** — §8.2 choice 5b's two
sentences, computed over the produced day rather than read off the definition. -/
theorem the_reservation_row_carries_no_energy :
    ((dayPlan theRunningRequest).segments.filter (fun s => s.val.flags.current)).map
        (fun s => (s.val.kind, s.val.energy, s.val.planned))
      = [(SegKind.block, none, some 70)] := by
  decide

set_option maxRecDepth 40000 in
/-- **The day assigns the running block after `now`, and nothing else** — the non-vacuity
witness for `Planner.the_day_assigns_nothing_after_now_but_the_running_block`, and the reason
that tripwire is a statement about a non-empty set.  `PlannerWit.the_witness_assigns_nothing
_after_now` is the same computation at the request with nothing running. -/
theorem the_reserved_day_assigns_the_running_block :
    assignedFrom (dayPlan theRunningRequest) theRunningRequest.now.sec = [['m','1']] := by
  decide

set_option maxRecDepth 40000 in
/-- **The battery passes at a request whose day holds a Block row the PLANNER placed.**

This is the half of README gap **396** the W-14 land step left open.  `the_battery_passes_at
_the_witness` above answers it for the replayed past; this answers it for §8.2 choice 5b, and
the difference matters: six of the seven checks were discharged by
`PlanCheck.dayPlan_ok_core`'s `hnopast` *and* by the day having no planner-placed Block at all,
so nothing in the stage had yet shown a checker meeting a row the planner is responsible for.
Here `oneBlockAtATime` compares the reservation against `block_min`, `noBlockOverAWall` puts it
beside the calendar's meeting, `noOverbook` runs its `withoutActive` filter on a row that
really is the running one, and `noDemandingAfterWindDown` has §16's evening to compare with. -/
theorem the_battery_passes_at_the_reserved_day :
    PlanCheck.planOkCore theRunningRequest (dayPlan theRunningRequest) = true := by
  decide

/-- The day with the reservation run half an hour past the block it is in. -/
def stretchTheReservation (s : WfSeg) : WfSeg :=
  if s.val.flags.current then Planner.segOf { s.val with stop := s.val.stop + 1800 } else s

def theOverrunDay : DayPlan :=
  { dayPlan theRunningRequest with
    segments := (dayPlan theRunningRequest).segments.map stretchTheReservation }

set_option maxRecDepth 40000 in
/-- **It bites on the row the planner placed**: let the reservation run seventy minutes — the
whole remaining estimate, which is what the fork's `current_block_end` refuses — and
`oneBlockAtATime` refuses the day.  A checker that only ever answered `true` about the
replayed past would not have caught this. -/
theorem the_battery_bites_on_the_reservation :
    PlanCheck.oneBlockAtATime theRunningRequest theOverrunDay = false ∧
      PlanCheck.planOkCore theRunningRequest theOverrunDay = false := by
  decide

/-! ############################################################################
## 8. `plan_reserves_one_block_at_a_time` as stage 6 wrote it is REFUTED
############################################################################ -/

/-- The same Wednesday with `[day] block_min` shortened to half an hour — a config edit a user
makes after a morning of hour-long blocks.  Nothing else moves: `Planner.dayRows` does not read
`block_min` at all (steps 1 and 2 place walls, the past, the routines and the evening), so the
day is the five rows of `the_witness_day_is_two_replayed_blocks_the_written_wall_and_the
_evening` with a *shorter* declared block. -/
def theShortBlockRequest : PlanReq :=
  { theRequest with
    look := { theRequest.look with
      day := { theRequest.look.day with
        cut := { theRequest.look.day.cut with blockMin := 30 } } } }

set_option maxRecDepth 40000 in
/-- The witness, computed: a Block row of sixty minutes on a day whose `block_min` is thirty. -/
theorem the_short_block_day_holds_a_block_longer_than_a_block :
    ((dayPlan theShortBlockRequest).segments.any (fun s =>
        s.val.kind == SegKind.block &&
          decide ((dayPlan theShortBlockRequest).blockMin * 60 < s.val.stop - s.val.start)))
      = true := by
  decide

/-- **§8.3's E1 as `Goals.lean` wrote it is FALSE** (AGENTS §3.1 item 3, D5), and the reason is
`PlanCheck`'s own finding 1 (README gap 385): the day's Block rows include the ones
`Planner.pastRows` replays from the log, and *"a Block the log holds can run longer than
`block_min` … none of it the planner's doing"*.  `Planner.plan_reserves_one_block_at_a_time` is
the restatement — over the Block rows that start at or after `now`, which is the fork's own
`assigned_set(day, w.now)` restriction — and it ships in the same commit as this. -/
theorem plan_reserves_one_block_at_a_time_as_stage_6_wrote_it_is_refuted :
    ¬ (∀ (r : PlanReq) (s : WfSeg), s ∈ (dayPlan r).segments → s.val.kind = SegKind.block →
        s.val.stop - s.val.start ≤ (dayPlan r).blockMin * 60) := by
  intro h
  have hb := the_short_block_day_holds_a_block_longer_than_a_block
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
  obtain ⟨s, hs, hk, hlong⟩ := hb
  exact absurd (h theShortBlockRequest s hs hk) (by omega)


/-! ############################################################################
## 9. §8.2 step 4, run rather than argued (stage 6 step P4, AGENTS §5.2)

Every law in `Planner.lean`'s step-4 section is a `∀` over a request.  The witnesses below are
`decide` over one, and they are written so that **a wrong value fails them, not only a missing
name** — README gap 577's lesson, which cost a whole repair step: inverting the `overdue` field
in the host's `cand_json` left all 1,331 Rust tests green while `tm plan` visibly re-ranked.
So each fact this step derives has a companion that **perturbs** it and asserts the answer moves.

The candidates deliberately do **not** enter §7.3's pass (`Look.Cand.enters` wants a due *and*
no placement window), because the EDF arithmetic already has stage 5's own witness
(`Look.priorities_on_a_witness`, at `witnessCaps`) and re-running it here would be a second
copy of that measurement — and would force `Look.lookahead witInput` inside a `decide`.  What
is new at P4 is the **key**, and the key is what these pin.
############################################################################ -/

/-- **Today's wall**, as fork `collect_candidates` marks it: the nine plain but for
`wall_today`, which it sets when the Interval's span covers today — and `^g1`'s does
(`lookWallPlan` is the §4.3 Wednesday's calendar).  Without it `priority::sorted_candidates`
leaves the wall out of the assignment order, which is exactly what P5a's filter does. -/
def todaysWallFacts : Look.WfPlanFacts :=
  ⟨{ Look.PlanFacts.unconstrained with wallToday := true }, by decide⟩

/-- §7.4's six: the calendar's own wall `^g1` (the one item `lookWallPlan` holds, so its line
order is a real one), an optional, an overdue instance, a mandatory instance, and two plain
`rank` candidates whose `k` differs — `^r1` carries a written `!1` and `^r2` takes
`default_priority`.  The dated ones carry a placement window, which is what keeps them out of
the pass without making their `due` a lie. -/
def witCands : List (Look.Cand × Option Look.Floor) :=
  [(⟨['g','1'], 3, none,   60, some 739870, false, true,  false, false, false, false, none, todaysWallFacts⟩, none),
   (⟨['o'],     3, none,   20, some 739870, false, false, true,  false, false, false, none, Look.wfUnconstrained⟩, none),
   (⟨['o','d'], 3, none,   30, some 739870, true,  false, false, true,  false, false, none, Look.wfUnconstrained⟩, none),
   (⟨['m'],     3, none,   30, some 739870, true,  false, false, false, true,  false, none, Look.wfUnconstrained⟩, none),
   (⟨['r','1'], 3, some 0, 50, none,        false, false, false, false, false, false, none, Look.wfUnconstrained⟩, none),
   (⟨['r','2'], 3, none,   50, none,        false, false, false, false, false, false, none, Look.wfUnconstrained⟩, none)]

/-- The §4.3 Wednesday with six candidates on the wire. -/
def theRankingRequest : PlanReq := { theRequest with cands := ⟨witCands, by decide⟩ }

def witReqInCands : PlanReqIn := { witReqIn with cands := witCands }

/-- **The builder accepts it** — the candidates go through `Capped.ofList?`, the wire's own cap. -/
theorem witBuildsCands : mkPlanReq? witReqInCands = .ok theRankingRequest := by
  obtain ⟨ht, hz, hd, hw, -⟩ := witInput_fields
  unfold mkPlanReq? witReqInCands witReqIn theRankingRequest theRequest
  simp only [lookWallPlan_loads, witInput_decodes]
  rw [if_neg (by
    rw [hw, hz, hd]
    simp only [Look.DayCfg.shipped, Look.CutCfg.shipped, ne_eq]
    exact not_not_intro the_look_wall_calendar_indexes_one_wednesday_wall.symm)]
  rw [hz, ht, witRun_resumes]
  simp only [mkRoutines?_of_none]
  rfl

/-- The ids of a request's answers, in §7.4's order. -/
def rankedIds (r : PlanReq) : List Id := r.rankedCands.map (fun x => x.out.out.cand.id)

/-- The `(id, p)` rows the day carries, with `p` as a number. -/
def priorityRows (r : PlanReq) : List (Id × Nat) :=
  (dayPlan r).priorities.val.map (fun q => (q.1, q.2.val))

/-- **§7.2's answer for each of the six, computed** — the *values*, not the shape.  The wall is
off the scale; the optional is `5`; overdue and mandatory are `0`; `^r1`'s written `!1` gives
`k = 1` and `p = k + 2 = 3`, and `^r2` takes `default_priority = 3` and lands on `5`.  Every one
of those numbers is a different row of §7.2's table, so a table read off the wrong row shows
here. -/
theorem the_ranking_requests_answers_are_stage_fives :
    theRankingRequest.candAnswers.map (fun o => (o.out.cand.id, o.out.p, o.out.k)) =
      [(['g','1'], none, 3), (['o'], some 5, 3), (['o','d'], some 0, 3),
       (['m'], some 0, 3), (['r','1'], some 3, 1), (['r','2'], some 5, 3)] := by
  decide

/-- **And §7.4 orders them: the wall first, then `p`, then the line order, then the request
position.**  `^od` and `^m` tie at `p = 0` and neither is in the plan, so the tie falls all the
way through to the request index and `^od` (position 2) keeps its place ahead of `^m`
(position 3) — the fork's `keyed.sort()` on `((u8, (p, root, own)), i)`.  `^o` and `^r2` tie at
`p = 5` and break the same way. -/
theorem the_ranking_request_is_ordered :
    rankedIds theRankingRequest =
      [['g','1'], ['o','d'], ['m'], ['r','1'], ['o'], ['r','2']] := by
  decide

/-- **The day carries those `p`s, in request order, and the wall is not among them** — fork
`day.priorities = cands.zip(&prios)`, less the row §7.2 puts off the scale. -/
theorem the_ranking_requests_day_carries_its_priorities :
    priorityRows theRankingRequest =
      [(['o'], 5), (['o','d'], 0), (['m'], 0), (['r','1'], 3), (['r','2'], 5)] := by
  decide

/-- **`^g1` is the one candidate the plan holds, and its key carries the plan's own line
order.**  The other five are not in this plan, which is fork `order`'s
`unwrap_or((usize::MAX, usize::MAX))` — here `none`, and `siteNums` puts it last. -/
theorem the_ranking_request_reads_the_plans_line_order :
    theRankingRequest.ownSite ['g','1'] = some ⟨0, 0⟩ ∧
    theRankingRequest.rootSite ['g','1'] = some ⟨0, 0⟩ ∧
    theRankingRequest.ownSite ['r','1'] = none := by
  decide

/-! ### The perturbations: a wrong VALUE fails, not only a missing name (gap 577) -/

/-- The same request with one candidate's one field changed. -/
def withCandAt (r : PlanReq) (i : Nat) (f : Look.Cand → Look.Cand) : PlanReq :=
  { r with cands := ⟨r.cands.val.zipIdx.map (fun x => if x.2 = i then (f x.1.1, x.1.2) else x.1),
      by
        refine Nat.le_trans ?_ r.cands.property
        simp⟩ }

/-- **Inverting `overdue` re-ranks the day.**  Position 2 is `^od`; with its `overdue` flag
cleared §7.2 answers on the `rank` line instead (`p = k + 2 = 5`) and it falls from second to
last.  This is exactly the mutation README gap 577 applied to `cand_json` — there it left 1,331
Rust tests green. -/
theorem clearing_overdue_moves_the_candidate :
    rankedIds (withCandAt theRankingRequest 2 (fun c => { c with overdue := false })) =
      [['g','1'], ['m'], ['r','1'], ['o'], ['o','d'], ['r','2']] ∧
    rankedIds (withCandAt theRankingRequest 2 (fun c => { c with overdue := false })) ≠
      rankedIds theRankingRequest := by
  decide

/-- **And inverting `mandatory` does too**, on the row below it — so the two flags are read
separately and not through one another. -/
theorem clearing_mandatory_moves_the_candidate :
    rankedIds (withCandAt theRankingRequest 3 (fun c => { c with mandatory := false })) =
      [['g','1'], ['o','d'], ['r','1'], ['o'], ['m'], ['r','2']] := by
  decide

/-- **A candidate that stops being a wall stops being first**, whatever its `p`: the key's
leading digit is the whole of §8.2 step 1's precedence. -/
theorem clearing_wall_moves_it_off_the_front :
    rankedIds (withCandAt theRankingRequest 0 (fun c => { c with wall := false })) =
      [['o','d'], ['m'], ['r','1'], ['o'], ['r','2'], ['g','1']] := by
  decide

/-- **The root's written `!k` is read, not defaulted**: take `^r1`'s away and its `p` goes from
`3` to `5`, and it falls behind `^o`.  A `kOf` that ignored `rootPrio` would pass every
name-shaped test and fail this one. -/
theorem taking_the_written_k_away_moves_the_candidate :
    rankedIds (withCandAt theRankingRequest 4 (fun c => { c with rootPrio := none })) =
      [['g','1'], ['o','d'], ['m'], ['o'], ['r','1'], ['r','2']] ∧
    (withCandAt theRankingRequest 4 (fun c => { c with rootPrio := none })).candAnswers.map
        (fun o => o.out.p) = [none, some 5, some 0, some 0, some 5, some 5] := by
  decide

/-- **§7.4's hysteresis is read from the candidate's own `yesterday`**: give `^r1` a stored `6`
and its `p` is held at `5` — one bin better than yesterday — instead of dropping to `3`, which
moves it behind `^o`.  `Prio.hysteresis_holds_one_step_back` is the rule; this is it on the
produced order. -/
theorem yesterdays_priority_holds_the_candidate_back :
    (withCandAt theRankingRequest 4 (fun c => { c with yesterday := some 6 })).candAnswers.map
        (fun o => o.out.p) = [none, some 5, some 0, some 0, some 5, some 5] ∧
    rankedIds (withCandAt theRankingRequest 4 (fun c => { c with yesterday := some 6 })) =
      [['g','1'], ['o','d'], ['m'], ['o'], ['r','1'], ['r','2']] := by
  decide

/-- `witCands` with the two `p = 0` candidates exchanged on the wire, and nothing else. -/
def witCandsSwapped : List (Look.Cand × Option Look.Floor) :=
  [(⟨['g','1'], 3, none,   60, some 739870, false, true,  false, false, false, false, none, todaysWallFacts⟩, none),
   (⟨['o'],     3, none,   20, some 739870, false, false, true,  false, false, false, none, Look.wfUnconstrained⟩, none),
   (⟨['m'],     3, none,   30, some 739870, true,  false, false, false, true,  false, none, Look.wfUnconstrained⟩, none),
   (⟨['o','d'], 3, none,   30, some 739870, true,  false, false, true,  false, false, none, Look.wfUnconstrained⟩, none),
   (⟨['r','1'], 3, some 0, 50, none,        false, false, false, false, false, false, none, Look.wfUnconstrained⟩, none),
   (⟨['r','2'], 3, none,   50, none,        false, false, false, false, false, false, none, Look.wfUnconstrained⟩, none)]

/-- **And the request position is a real tie-break, not decoration**: swap the two `p = 0`
candidates on the wire and the order swaps with them.  Two candidates that agree on every key
component but their arrival order are exactly §5.3's carried instance and today's fresh one. -/
theorem the_request_order_breaks_a_tie :
    rankedIds { theRankingRequest with cands := ⟨witCandsSwapped, by decide⟩ } =
      [['g','1'], ['m'], ['o','d'], ['r','1'], ['o'], ['r','2']] := by
  decide


/-! ### §8.2 step 5's filter, one cause at a time (P5b-i, README gap 602)

`PlanReq.rankedCands` now applies fork `priority::sorted_candidates`' own filter, which is what
P5a's wire made possible.  Five causes drop a candidate and **each is given its own witness in
which that cause is the only thing that differs** — the shape README gap 677 was paid for.  The
order of the survivors never moves, which is the other half of the claim: the filter runs before
the sort and filtering a sorted list changes no pair's order. -/

/-- The same request with one candidate's **nine** replaced, nothing else touched. -/
def withFactsAt (r : PlanReq) (i : Nat) (g : Look.WfPlanFacts) : PlanReq :=
  withCandAt r i (fun c => c.withPlan g)

/-- `[?]` — waiting for an event (§5.1). -/
def waitingFacts : Look.WfPlanFacts :=
  ⟨{ Look.PlanFacts.unconstrained with state := Status.live .world }, by decide⟩

/-- `[x]` — a closed state. -/
def doneFacts : Look.WfPlanFacts :=
  ⟨{ Look.PlanFacts.unconstrained with state := Status.settled .done }, by decide⟩

/-- One unsatisfied `after:` dependency (§5.5). -/
def blockedFacts : Look.WfPlanFacts :=
  ⟨{ Look.PlanFacts.unconstrained with blockedBy := [.item ['k', '7']] }, by decide⟩

/-- A `max:` of sixty minutes with sixty spent (§6.2). -/
def capReachedFacts : Look.WfPlanFacts :=
  ⟨{ Look.PlanFacts.unconstrained with cap := some ⟨60, 60⟩ }, by decide⟩

/-- The same `max:` with thirty minutes left. -/
def capLeftFacts : Look.WfPlanFacts :=
  ⟨{ Look.PlanFacts.unconstrained with cap := some ⟨60, 30⟩ }, by decide⟩

/-- **Each of the four item causes drops the candidate, one at a time.**  Position 4 is `^r1`,
which stands fourth in the unfiltered order; each line below changes exactly one of its nine and
nothing else, and `^r1` leaves.  A filter that read `state` for `blocked_by`, or `cap` for
`state`, would pass one line and fail another. -/
theorem each_cause_of_ineligibility_drops_the_candidate :
    rankedIds (withFactsAt theRankingRequest 4 waitingFacts)
      = [['g','1'], ['o','d'], ['m'], ['o'], ['r','2']] ∧
    rankedIds (withFactsAt theRankingRequest 4 doneFacts)
      = [['g','1'], ['o','d'], ['m'], ['o'], ['r','2']] ∧
    rankedIds (withFactsAt theRankingRequest 4 blockedFacts)
      = [['g','1'], ['o','d'], ['m'], ['o'], ['r','2']] ∧
    rankedIds (withFactsAt theRankingRequest 4 capReachedFacts)
      = [['g','1'], ['o','d'], ['m'], ['o'], ['r','2']] := by
  decide

/-- **And the `max:` cause turns on the two numbers, not on the cap's presence**: the same
candidate with sixty minutes capped and *thirty* spent is eligible and keeps its place.  Without
this line `capReachedFacts` above would be satisfied by a filter that dropped every capped item.
-/
theorem a_cap_with_minutes_left_keeps_the_candidate :
    rankedIds (withFactsAt theRankingRequest 4 capLeftFacts) = rankedIds theRankingRequest := by
  decide

/-- **Another day's wall is dropped, and today's is not.**  Position 0 is `^g1`, the calendar's
Wednesday wall; clearing `wall_today` — one boolean, nothing else — removes it from the
assignment order, and it is the only candidate whose removal this boolean can cause. -/
theorem a_wall_that_is_not_todays_is_dropped :
    rankedIds (withFactsAt theRankingRequest 0 Look.wfUnconstrained)
      = [['o','d'], ['m'], ['r','1'], ['o'], ['r','2']] ∧
    rankedIds (withFactsAt theRankingRequest 0 Look.wfUnconstrained)
      ≠ rankedIds theRankingRequest := by
  decide

/-- **`wall_today` is read only of a wall.**  Setting it on `^r1`, which is not a wall, changes
nothing — so the theorem above is about the conjunction the fork writes
(`!c.is_wall || c.wall_today`) and not about the flag alone. -/
theorem wall_today_is_read_only_of_a_wall :
    rankedIds (withFactsAt theRankingRequest 4 todaysWallFacts) = rankedIds theRankingRequest := by
  decide

/-- **The filter drops and never reorders.**  Every one of the five perturbations above leaves
the survivors in the order they had, which is the claim that makes `rankedCands`' sortedness
laws unchanged by P5b-i: filtering a sorted list by any predicate is a sublist of it. -/
theorem the_filter_keeps_the_survivors_in_order :
    (rankedIds (withFactsAt theRankingRequest 4 waitingFacts)).Sublist
      (rankedIds theRankingRequest) ∧
    (rankedIds (withFactsAt theRankingRequest 0 Look.wfUnconstrained)).Sublist
      (rankedIds theRankingRequest) := by
  decide

/-! ############################################################################
## 10. §8.3's wall law is FALSE as stage 6 wrote it — the witness (W-17, track G)
############################################################################

`PlanCheck`'s header records finding 1 (README gap 385): *"a Block the log holds can run
longer than `block_min`, **can sit under a wall**, can overlap a break and can exhaust the
budget — none of it the planner's doing"*.  Step P3 took the first clause and refuted E1 with
it.  This is the second clause, taken the same way, and the witness needs **one record**: move
the calendar's meeting onto a block the morning's log already holds.

Nothing about the log changes — `witRun` is the same six lines — and nothing about the plan
changes.  Only the wall index the request carries moves, which is the same lever
`theShortBlockRequest` pulls on `[day] block_min`. -/

/-- The §4.3 Wednesday with the meeting moved to **07:20–07:50**, inside the hour the log
records as worked on `m1` (07:05–08:05).  A real calendar sync does exactly this: an event
arrives on a slot the day has already spent. -/
def theMorningWallRequest : PlanReq :=
  { theRequest with
    look := { theRequest.look with
      walls := [⟨['g','1'], 739867, 739867,
                 (Cal.instantOf Cal.chicago 739867 440).sec,
                 (Cal.instantOf Cal.chicago 739867 440).sec,
                 (Cal.instantOf Cal.chicago 739867 470).sec⟩] } }

set_option maxRecDepth 40000 in
/-- The witness, computed: the day the planner produces holds a Block row and a Wall row that
**overlap**, and the battery says so on its own (`noBlockOverAWall = false`) rather than being
told. -/
theorem the_morning_wall_day_lays_a_block_across_a_wall :
    (∃ b ∈ (dayPlan theMorningWallRequest).segments,
      ∃ w ∈ (dayPlan theMorningWallRequest).segments,
        b.val.kind = SegKind.block ∧ w.val.kind = SegKind.wall ∧
          w.val.start < b.val.stop ∧ b.val.start < w.val.stop) ∧
      PlanCheck.noBlockOverAWall theMorningWallRequest (dayPlan theMorningWallRequest) = false := by
  decide

/-- **§8.3's "no Block over a Wall" as `Goals.lean` wrote it is FALSE** (AGENTS §3.1 item 3,
D5), for the reason step P3 refuted E1 with: the day's Block rows include the ones
`Planner.pastRows` replays from the log, and a Block the log holds can sit under a wall the
calendar acquired afterwards.  `PlanCheck.plan_places_no_block_over_a_wall` is the restatement
— over the Block rows that start at or after `now`, the fork's own `assigned_set(day, w.now)`
restriction — and it ships in the same commit as this. -/
theorem plan_places_no_block_over_a_wall_as_stage_6_wrote_it_is_refuted :
    ¬ (∀ (r : PlanReq) (b w : WfSeg), b ∈ (dayPlan r).segments → w ∈ (dayPlan r).segments →
        b.val.kind = SegKind.block → w.val.kind = SegKind.wall →
        b.val.stop ≤ w.val.start ∨ w.val.stop ≤ b.val.start) := by
  intro h
  obtain ⟨b, hbmem, w, hwmem, hbk, hwk, h1, h2⟩ :=
    the_morning_wall_day_lays_a_block_across_a_wall.1
  rcases h theMorningWallRequest b w hbmem hwmem hbk hwk with hd | hd <;> omega

/-! ############################################################################
## 11. README gap 396, the other nine: the census, and eleven bites (W-17)
############################################################################

W-14 asked whether the battery gives an opinion of its own.  W-15 answered it for
`wallsUnmoved` and `noBlockOverAWall`, W-16 for `oneBlockAtATime` on the row the *planner*
places.  **Three of eleven.**  This section answers it for the other eight and, more
importantly, says out loud which of the eleven are checking anything at all over a day
`Planner.dayPlan` really produces — because *"a check no input can fail"* is §9.2's disguised
gap and a checker whose quantifier is empty is exactly that, whether or not a `can_fail`
witness exists for it over a hand-built day.

**The two are different questions and this section keeps them apart.**

* **Non-vacuous** — the checker's quantifier has a subject on the day the planner produced, so
  the `true` it returns was earned.  `the_battery_census_over_a_produced_day` computes the
  populations; **five** of the eleven have one over the day at `theStoredRequest` and six do
  not.  (This read *"six … and five do not"* until the W-17 repair: it counted `wallsUnmoved`,
  whose subject is there at `theRequest` and at `theRunningRequest` but **not** at the request
  the census is stated over — the caveat the table carried and the count did not.  The census
  now computes that conjunct too.  And it read *"each of the six waits on a named later step"*
  until **W-18**, which is the sentence section **14** is about: **two of the six wait on a
  request, not on a step**, and at `theCensusRequest` the ratio is **seven of eleven**.  (This
  read *"section 13"* until W-18's repair step: track G wrote the line and the section, the
  merge renumbered the section to 14 because `## 13.` already existed on the branch, and the
  sweep for citations looked in every file **but this one**.))
* **Bites** — some mutation of that same produced day is refused.  `the_battery_bites_*`
  below, with W-15's and W-16's, make it **eleven of eleven**.

**No second copy of any placement rule is written here** (AGENTS §5.3, and the W-14 land step's
own refusal): every mutation is a `List.map` or `List.filter` over the day
`Planner.dayPlan` built, and every verdict is `PlanCheck`'s own checker evaluating. -/

/-- **A store that holds the ids the morning actually worked.**  `Boundary.lookWallPlan` is a
one-line calendar, so `effectiveCi` answers §3.1's default of three for the replayed rows'
`m1`/`m2` and the store has **one** id in it — which leaves **seven** of the eleven checkers
with nothing to range over at `theRunningRequest`, **three** of them for reasons that are
about the *witness* and not about the *planner*.

*(**W-19 corrected this sentence and computed it.**  It read *"which leaves five of the eleven
checkers with nothing to range over for reasons that are about the witness and not about the
planner"* — a number that matches no reading of any census in the repository, and one nothing
computed.  `the_one_id_store_gives_neither_comparison_a_subject` measures the half that was
never measured: a one-id store gives `PlanCheck.monotoneInRank` and `PlanCheck.hotBeforeQueue`
no pair at all.  Four of eleven have a subject there; seven do not; three of the seven are the
witness's doing and four are gap 650's.  README gap 852.)*

This is `Boundary.undoWitnessRequest`'s two tasks, reused verbatim but for one word: `m1` and
`m2`, `ci:5`, two ranked siblings of one document, and `hot` on the first.  The ids are the
ones `witLines` records as started and done, so the day the planner produces assigns items the
store really holds. -/
def storedWitness : List ReqDoc :=
  [⟨"week/2026-W37.md", some ⟨week, 35⟩,
      ["# Tasks".toList, "- [ ] 5 6b Finish the report ^m1 hot".toList,
       "- [ ] 5 6b Write the tests ^m2".toList]⟩,
   ⟨"month/2026-09.md", some ⟨month, 8⟩, ["# Outcomes".toList]⟩]

set_option maxRecDepth 40000 in
theorem the_stored_witness_loads : loadsOk storedWitness = true := by decide

/-- The loaded store.  Total by `the_stored_witness_loads`: the error branch is refuted, not
defaulted (`Boundary.lookWallPlan`'s pattern). -/
def storedPlan : WfPlan :=
  match h : loadPlan storedWitness with
  | .ok p => p
  | .error _ => absurd the_stored_witness_loads (by simp [loadsOk, h])

set_option maxRecDepth 8000 in
/-- What the store holds, computed: two siblings of one document, both at `ci:5`, ranked 1 and
2, and `hot` on `m1` alone. -/
theorem the_stored_witness_holds_two_ranked_siblings :
    storedPlan.val.store.dom = [['m','2'], ['m','1']] ∧
      (effectiveCi storedPlan.val ['m','1']).val = 5 ∧
      (effectiveCi storedPlan.val ['m','2']).val = 5 ∧
      rootPrio storedPlan.val ['m','1'] = rootPrio storedPlan.val ['m','2'] ∧
      (storedPlan.val.store.get ['m','1']).map (fun e => (e.val.live.doc, e.val.live.rank,
          e.val.flags)) = some (0, 1, [Field.Flag.hot]) ∧
      (storedPlan.val.store.get ['m','2']).map (fun e => (e.val.live.doc, e.val.live.rank,
          e.val.flags)) = some (0, 2, []) := by
  decide

/-- The §4.3 Wednesday at 14:00 with `m1` running **and** a store that holds `m1` and `m2`. -/
def theStoredRequest : PlanReq := { theRunningRequest with plan := storedPlan }

/-- The permissive eligibility — the one the battery is instantiated at until **P5** writes
Planner.eligibleAt (README gap 365).  It is named once here rather than spelled at each use,
so the day P5 lands there is one place to change. -/
abbrev permissive : PlanCheck.Eligible := fun _ _ _ _ => true

set_option maxRecDepth 40000 in
/-- **The day, and the battery's verdict on it.**  Six rows: the two replayed Blocks, the
written wall, choice 5b's reservation and §16's evening — the same day
`the_reserved_day_is_the_witness_day_and_the_running_block` computes, with a different store
behind it. -/
theorem the_stored_day_passes_the_whole_battery :
    PlanCheck.planOk permissive theStoredRequest (dayPlan theStoredRequest) = true := by
  decide

set_option maxRecDepth 40000 in
/-- **The census: what each of the eleven actually ranges over, on the day the planner
produced.**  Every line is a population, computed; the prose beside each says which checker it
makes vacuous and which step ends that.

* three Block rows and one Wall row — `noOverbook`, `oneBlockAtATime` and `noBlockOverAWall`
  have subjects;
* **the Wall row's item is NOT in this store** — `wallsUnmoved` takes `wallUnmoved`'s
  `store.get i = none` branch and is **vacuous here**.  It has a subject at `theRequest` and at
  `theRunningRequest`, whose store holds the calendar's `^g1`
  (`the_battery_census_at_the_reserved_day`), and not at this request, whose store was swapped
  for the two tasks the morning worked.  That is the conjunct below and it is why the honest
  count over *this* day is **five of eleven**, not six (W-17 repair);
* `assignedFrom … now` holds one item, so one of the three Blocks is the **planner's**;
* **no Break row** — `noBlockOverABreak` is vacuous **at this request**, because `witLines`
  records no `break`; the *cut's* breaks reach the day only when work touches them
  (`kept_breaks`, README gap 551), which is **P5**, but the *log's* breaks reach it today
  (`Planner.a_break_row_is_a_replayed_row` is the rule, read the other way).  **W-18:** gap
  650 gave this checker's emptiness to P5 and that was wrong — `theCensusRequest` ends it with
  one extra log line;
* **no row carries a slot energy** — `energyFilterOk` is vacuous; a Block gets one when the
  assign fold puts it in an energised slot, which is **P5**, and
  `PlanCheck.no_block_row_of_the_day_carries_a_slot_energy` proves no request can beat it
  there (W-18).  *(The population below is "rows carrying an energy", which over-counts: a
  Routine row carries `PlanReq.routineEnergy` and `energyOk` never reads it.  Both are zero
  here — this witness has no routine — and the theorem, not the population, is what rules the
  checker's own subject out.)*;
* **no Block at or after the wind-down** — `noDemandingAfterWindDown` is vacuous; **P5/P7**,
  and `PlanCheck.no_block_row_of_the_day_reaches_the_wind_down` proves it of every request
  (W-18): a WindDown row exists only while `now < wind_down`, and every Block row starts at or
  before `now`;
* **no Batch row** — `batchDoesNotReachPast` is vacuous; **P5**, and
  `PlanCheck.the_day_has_no_batch_row` proves it of every request (W-18);
* **`diagnostics.impossible` is empty** — `impossibleKept` is vacuous; **P8**, the step that
  fills it (gap 367's second half; its first landed at P4 as `Planner.edfNumbers`, and this
  line read "**P4**" until the W-17 repair — P4 landed without ending it).
  `PlanCheck.the_day_names_no_impossible_item` proves it of every request (W-18), and it is
  `rfl`;
* the store holds two ranked siblings and one of them is `hot`, and both are assigned, so
  `monotoneInRank` and `hotBeforeQueue` have real pairs. -/
theorem the_battery_census_over_a_produced_day :
    ((dayPlan theStoredRequest).segments.filter
        (fun s => s.val.kind == SegKind.block)).length = 3 ∧
      ((dayPlan theStoredRequest).segments.filter
        (fun s => s.val.kind.isWork)).length = 3 ∧
      ((dayPlan theStoredRequest).segments.filter
        (fun s => s.val.kind == SegKind.wall)).length = 1 ∧
      assignedFrom (dayPlan theStoredRequest) theStoredRequest.now.sec = [['m','1']] ∧
      ((dayPlan theStoredRequest).segments.filter
        (fun s => s.val.kind == SegKind.wall)).map
          (fun s => (s.val.item.bind
            (fun i => theStoredRequest.plan.val.store.get i)).isSome) = [false] ∧
      (dayPlan theStoredRequest).segments.filter (fun s => s.val.kind == SegKind.brk) = [] ∧
      (dayPlan theStoredRequest).segments.filter (fun s => s.val.energy.isSome) = [] ∧
      (dayPlan theStoredRequest).segments.filter (fun s => s.val.kind == SegKind.block &&
        decide (theStoredRequest.windDownSec ≤ s.val.start)) = [] ∧
      (dayPlan theStoredRequest).diagnostics.impossible.val = [] ∧
      assignedOf (dayPlan theStoredRequest) = [['m','1'], ['m','2'], ['m','1']] := by
  decide

/-! ### The eight mutations the other eight checkers refuse

Each is a `List.map`, a `List.filter` or one field of the day `Planner.dayPlan` built — never
a hand-written day, which is what `PlanCheck`'s `wDay` witnesses already are and what these
are deliberately not. -/

/-- A budget of nothing, against a day that has already spent an hour on `m2`. -/
def theSpentDay : DayPlan := { dayPlan theStoredRequest with budgetBlocks := 0 }

/-- `m2`'s block given a slot energy of zero, against its `ci:5`.  It is `m2` and not `m1`
because `m1` is the running item and `energyOk` excuses the reservation by name (design §6.3
row 2). -/
def dimIt (s : WfSeg) : WfSeg :=
  if s.val.item = some (['m','2'] : Id) then Planner.segOf { s.val with energy := some 0 } else s

def theDimDay : DayPlan :=
  { dayPlan theStoredRequest with segments := (dayPlan theStoredRequest).segments.map dimIt }

/-- The written wall turned into a break, with `m1`'s first block laid across it. -/
def breakIt (s : WfSeg) : WfSeg :=
  if s.val.kind = SegKind.wall then Planner.segOf { s.val with kind := SegKind.brk }
  else if s.val.item = some (['m','1'] : Id) then
    Planner.segOf { s.val with start := (Cal.instantOf Cal.chicago 739867 780).sec,
                               stop := (Cal.instantOf Cal.chicago 739867 800).sec }
  else s

def theBrokenDay : DayPlan :=
  { dayPlan theStoredRequest with segments := (dayPlan theStoredRequest).segments.map breakIt }

/-- `m2`'s `ci:5` block moved into the wind-down. -/
def lateIt (s : WfSeg) : WfSeg :=
  if s.val.item = some (['m','2'] : Id) then
    Planner.segOf { s.val with start := (Cal.instantOf Cal.chicago 739867 1300).sec,
                               stop := (Cal.instantOf Cal.chicago 739867 1310).sec }
  else s

def theLateDay : DayPlan :=
  { dayPlan theStoredRequest with segments := (dayPlan theStoredRequest).segments.map lateIt }

/-- The day with every row naming `m1` dropped: the item that ranks ahead of `m2`, and is the
`hot` one, vanishes while `m2` keeps its block.  That is the shipped bug §8.3's rank and HOT
laws are about — *"the skipped item simply never appears"*. -/
def theDroppedFirstDay : DayPlan :=
  { dayPlan theStoredRequest with
    segments := (dayPlan theStoredRequest).segments.filter
      (fun s => !decide (s.val.item = some (['m','1'] : Id))) }

/-- The same day, with `m1` named IMPOSSIBLE in the diagnostics it is missing from. -/
def theSilentlyDroppedDay : DayPlan :=
  { theDroppedFirstDay with
    diagnostics := { (dayPlan theStoredRequest).diagnostics with
      impossible := Capped.ofListTake [((['m','1'] : Id), 60)] } }

/-- The same day again, with `m2`'s row gathered into a batch that reached past `m1`. -/
def batchIt (s : WfSeg) : WfSeg :=
  if s.val.item = some (['m','2'] : Id) then
    Planner.segOf { s.val with kind := SegKind.batch ⟨[['m','2']], by decide⟩ }
  else s

def theBatchedDay : DayPlan :=
  { theDroppedFirstDay with segments := theDroppedFirstDay.segments.map batchIt }

set_option maxRecDepth 40000 in
/-- **Eight refusals, over eight mutations of the day the planner actually built.**  With
`the_battery_bites_at_the_witness` (W-15: `wallsUnmoved`, `noBlockOverAWall`,
`oneBlockAtATime`) and `the_battery_bites_on_the_reservation` (W-16: `oneBlockAtATime` on the
row the planner placed), **every one of the eleven now refuses something**. -/
theorem the_battery_bites_over_a_produced_day :
    PlanCheck.noOverbook theStoredRequest theSpentDay = false ∧
      PlanCheck.energyFilterOk theStoredRequest theDimDay = false ∧
      PlanCheck.noBlockOverABreak theStoredRequest theBrokenDay = false ∧
      PlanCheck.noDemandingAfterWindDown theStoredRequest theLateDay = false ∧
      PlanCheck.monotoneInRank permissive theStoredRequest theDroppedFirstDay = false ∧
      PlanCheck.hotBeforeQueue permissive theStoredRequest theDroppedFirstDay = false ∧
      PlanCheck.impossibleKept permissive theStoredRequest theSilentlyDroppedDay = false ∧
      PlanCheck.batchDoesNotReachPast permissive theStoredRequest theBatchedDay = false := by
  decide

set_option maxRecDepth 40000 in
/-- And the battery as a whole refuses each of them — `planOk` is `false` on all eight, so a
mutation that reaches any single checker reaches the conjunction the lift is about. -/
theorem the_whole_battery_refuses_each_mutation :
    PlanCheck.planOk permissive theStoredRequest theSpentDay = false ∧
      PlanCheck.planOk permissive theStoredRequest theDimDay = false ∧
      PlanCheck.planOk permissive theStoredRequest theBrokenDay = false ∧
      PlanCheck.planOk permissive theStoredRequest theLateDay = false ∧
      PlanCheck.planOk permissive theStoredRequest theDroppedFirstDay = false ∧
      PlanCheck.planOk permissive theStoredRequest theSilentlyDroppedDay = false ∧
      PlanCheck.planOk permissive theStoredRequest theBatchedDay = false := by
  decide

/-! ############################################################################
## 12. The new lift's five hypotheses, discharged at a request (W-17, track G)
############################################################################

`PlanCheck.dayPlan_ok_core_from_now` drops `dayPlan_ok_core`'s `hnopast` and keeps five
hypotheses.  **AGENTS §7.4 item 2 asks whether they are jointly satisfiable, and a theorem
whose hypotheses nothing can satisfy is §9.2's own disguised gap** — *"a precondition nothing
can satisfy, so the conclusion never fires"*.  It stayed invisible for a whole stage once.

So all five are discharged here at `theRunningRequest`, the §4.3 Wednesday at 14:00 with `m1`
running, and the lift is applied rather than admired:

* `hagree` — `mkPlanReq?_ok_wallsAgree` at the request the builder accepts;
* `hactive`, `hday` — `the_running_request_agrees`, already proved for E1;
* `hnowcal` — computed;
* `hplain` — proved, and it is the one that needed an argument rather than a `decide`: it
  quantifies over **every** `Id`, and what bounds it is that a `get` lands in the store's
  `dom` (`PlanCheck.mem_dom_of_get`), which here is one id.

And the day the lift is about is **not empty**: `the_restricted_day_keeps_the_reservation
_and_the_wall` computes the four rows that survive `withoutPast`, which are the wall, §8.2
choice 5b's reservation and §16's evening.  So `noBlockOverAWall` at that request really does
put a Block the planner placed beside a Wall the calendar wrote, and the `true` the lift
returns for it was earned. -/

set_option maxRecDepth 8000 in
/-- The store behind this request holds exactly one item and it is the calendar's meeting,
written without a `buffer:` — the two facts `hplain` turns on. -/
theorem the_only_dated_item :
    theRunningRequest.plan.val.store.dom = [['g','1']] ∧
      (theRunningRequest.plan.val.store.get ['g','1']).map
          (fun e => (e.val.shape, e.val.buffer))
        = some (Field.Shape.interval ⟨739867, ⟨770, by decide⟩⟩ ⟨739867, ⟨830, by decide⟩⟩,
                none) := by
  decide

set_option maxRecDepth 40000 in
/-- **`hplain`, discharged.**  The hypothesis quantifies over every `Id`, so it cannot be a
`decide`; what bounds it is `PlanCheck.mem_dom_of_get` — a `get` that succeeds lands in the
store's `dom`, and this store's `dom` is one id. -/
theorem the_running_request_is_plain :
    ∀ (i : Id) (e : Entity) (a b : Field.DT),
      theRunningRequest.plan.val.store.get i = some e →
      e.val.shape = Field.Shape.interval a b →
      e.val.buffer = none ∧
        theRunningRequest.dayStart ≤ (Cal.instantOf theRunningRequest.tz a.day a.time).sec ∧
        (Cal.instantOf theRunningRequest.tz b.day b.time).sec ≤ theRunningRequest.dayEnd ∧
        (Cal.instantOf theRunningRequest.tz a.day a.time).sec
          < (Cal.instantOf theRunningRequest.tz b.day b.time).sec ∧
        (Cal.instantOf theRunningRequest.tz b.day b.time).sec < LogStamp.yearEnd := by
  intro i e a b hget hsh
  obtain ⟨hdom, hval⟩ := the_only_dated_item
  have hmem := PlanCheck.mem_dom_of_get _ i e hget
  rw [hdom] at hmem
  simp only [List.mem_singleton] at hmem
  subst hmem
  rw [hget, Option.map_some] at hval
  have he := Option.some.inj hval
  have hsh0 : e.val.shape
      = Field.Shape.interval ⟨739867, ⟨770, by decide⟩⟩ ⟨739867, ⟨830, by decide⟩⟩ :=
    congrArg Prod.fst he
  have hbuf : e.val.buffer = none := congrArg Prod.snd he
  rw [hsh0] at hsh
  injection hsh with ha hb
  subst ha
  subst hb
  exact ⟨hbuf, by decide, by decide, by decide, by decide⟩

/-- `hnowcal`: the instant being planned is inside the calendar. -/
theorem the_running_request_is_inside_the_calendar :
    theRunningRequest.now.sec + 1 < LogStamp.yearEnd := by decide

/-- `hagree` for the request with a block running, as `theRequest_wallsAgree` is for the one
without.  Both come from the builder and neither is assumed. -/
theorem theRunningRequest_wallsAgree : theRunningRequest.wallsAgree = true :=
  mkPlanReq?_ok_wallsAgree witReqInRun theRunningRequest witBuildsRun

set_option maxRecDepth 40000 in
/-- **What `withoutPast` actually removes**, computed: the two replayed Blocks of the morning,
and nothing else.  The wall the calendar wrote, §8.2 choice 5b's reservation and §16's two
evening rows all stay — which is the point of the filter, since a Wall, a Break and the
wind-down are the **comparands** §8.3's laws put a Block beside, not the subjects of them. -/
theorem the_restricted_day_keeps_the_reservation_and_the_wall :
    (PlanCheck.withoutPast theRunningRequest (dayPlan theRunningRequest)).segments.map
        (fun s => (s.val.start, s.val.stop, s.val.kind, s.val.item))
      = [((Cal.instantOf Cal.chicago 739867 770).sec, (Cal.instantOf Cal.chicago 739867 830).sec,
          SegKind.wall, some (['g','1'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 840).sec, (Cal.instantOf Cal.chicago 739867 880).sec,
          SegKind.block, some (['m','1'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 1290).sec,
          (Cal.instantOf Cal.chicago 739867 1320).sec, SegKind.windDown, none),
         ((Cal.instantOf Cal.chicago 739867 1320).sec, (Cal.instantOf Cal.chicago 739868 0).sec,
          SegKind.sleep, none)] := by
  decide

/-- **The lift, fired.**  Every hypothesis of `PlanCheck.dayPlan_ok_core_from_now` is supplied
by a theorem above, so the five are jointly satisfiable and the conclusion is not vacuous
(AGENTS §7.4 item 2).  Nothing here is a `decide`: it is the general lift applied. -/
theorem the_lift_applies_at_the_running_request :
    PlanCheck.planOkCore theRunningRequest
      (PlanCheck.withoutPast theRunningRequest (dayPlan theRunningRequest)) = true :=
  PlanCheck.dayPlan_ok_core_from_now theRunningRequest theRunningRequest_wallsAgree
    the_running_request_agrees.1 the_running_request_agrees.2
    the_running_request_is_inside_the_calendar the_running_request_is_plain

set_option maxRecDepth 40000 in
/-- **The two assumed comparisons, computed on the day the lift is about** (W-19's repair
step).  `PlanCheck.dayPlan_ok_from_now_given_the_two_comparisons` takes `hrank` and `hhot` as
hypotheses and had **no instance in which all of its hypotheses hold**: the nearest computed
fact in the tree was `the_battery_passes_at_the_census_request`, which is `planOk` over the
**whole** day and not over `withoutPast`'s, and this file argues elsewhere that neither of
those two days implies the other.  That is AGENTS §7.4 item 2's question left unanswered about
the one theorem W-19 added with assumed hypotheses.  Here they are, at the reserved day, where
the other five hypotheses already have theorems. -/
theorem the_two_comparisons_hold_at_the_reserved_day :
    PlanCheck.monotoneInRank permissive theRunningRequest
        (PlanCheck.withoutPast theRunningRequest (dayPlan theRunningRequest)) = true ∧
      PlanCheck.hotBeforeQueue permissive theRunningRequest
        (PlanCheck.withoutPast theRunningRequest (dayPlan theRunningRequest)) = true := by
  decide

/-- **The two-comparison lift, fired.**  Seven hypotheses, every one of them a theorem above,
so the conclusion is not vacuous and the statement is not a promise about an empty domain.
Nothing here is a `decide` on the conclusion: it is the general lift applied.

It does **not** weaken `PlannerWit.dayPlan_ok_from_now_at_every_eligibility_is_refuted`, which
says the two hypotheses cannot be dropped for an arbitrary `el`; this says they are satisfiable
at one, which is the other half of the same question. -/
theorem the_two_comparison_lift_applies_at_the_reserved_day :
    PlanCheck.planOk permissive theRunningRequest
      (PlanCheck.withoutPast theRunningRequest (dayPlan theRunningRequest)) = true :=
  PlanCheck.dayPlan_ok_from_now_given_the_two_comparisons permissive theRunningRequest
    theRunningRequest_wallsAgree the_running_request_agrees.1 the_running_request_agrees.2
    the_running_request_is_inside_the_calendar the_running_request_is_plain
    the_two_comparisons_hold_at_the_reserved_day.1
    the_two_comparisons_hold_at_the_reserved_day.2

/-! ############################################################################
## 13. The root walk the key really does, and the census at the reserved day
   (W-17 repair step)
############################################################################

Two holes the W-17 auditors found, and they are the same hole twice: **a fact asserted in
prose beside a `decide` that could not see it.**  README gap 577's class, inside the two steps
written to close it.

**(a) §7.4's key compares the ROOT's line order before the item's own, and nothing in this
file could tell.**  `the_ranking_request_reads_the_plans_line_order` computes
`ownSite ^g1 = some ⟨0,0⟩ ∧ rootSite ^g1 = some ⟨0,0⟩` — the two are **equal**, and they are
equal (or both `none`) for every candidate of every witness the tree held.  So inverting
`Planner.CandKey.nums`' `siteNums k.root ++ siteNums k.own` to
`siteNums k.own ++ siteNums k.root` left **`check.sh` 7/7 and `cargo test --workspace`
1,337 passed / 0 failed / 9 ignored** — both re-measured under the inversion by the repair step
— while `#eval` shows the order flipping.  `theRootedRequest` below is the first request in
which the two orders **disagree**, and `the_root_order_decides_before_the_items_own` is the
`decide` the inversion fails.

**(b) The census stopped at `theStoredRequest`, and `PlanCheck.lean`'s header quoted a number
from a day nobody had counted.**  `the_battery_census_at_the_reserved_day` counts the same
populations over `dayPlan theRunningRequest` and over the `PlanCheck.withoutPast` day the new
lift is about, so both lifts' vacuity is a computed fact at the request their own doc comments
cite.  It is what `PlanCheck.dayPlan_ok_core_from_now`'s *"measured rather than asserted"*
paragraph names; that paragraph cited `the_battery_census_at_the_reserved_day` before
the theorem existed.  (Reflowed by W-18's land step so that `theorem` does not begin a
line: check 3's declaration grep is `^(@[...])?theorem ` and counted this prose as a
declaration whose extracted name was EMPTY -- AGENTS 6.3's `whose` trap, which that
section records as repaired once at `Cmd.lean:29-33` and which recurred here.  README
gap 773.)

**Nothing here re-implements a placement rule or a checker** (AGENTS §5.3): the plan goes
through `Boundary.loadPlan`, the candidates through `Look.prioritiesWithFloors` by way of
`PlanReq.candAnswers`, the order through `Planner.sortRanked`, and every population is a
`List.filter` over the day `Planner.dayPlan` built. -/

/-- **A plan whose root order is the REVERSE of its items' own order.**  Two week tasks, two
month outcomes, and the parents crossed: `^m1` is first in the week and its root `^O2` is
second in the month, `^m2` is second in the week and its root `^O1` is first.  That is the one
shape in which §7.4's `(root, own)` and a hypothetical `(own, root)` give different answers,
and `PlannerWit` had no such shape in it.

It is `storedWitness` widened by a `@parent` on each task and two outcome lines — the same two
documents, the same two ids, the same `ci:5`. -/
def rootedWitness : List ReqDoc :=
  [⟨"week/2026-W37.md", some ⟨week, 35⟩,
      ["# Tasks".toList,
       "- [ ] 5 6b Finish the report @O2 ^m1".toList,
       "- [ ] 5 6b Write the tests   @O1 ^m2".toList]⟩,
   ⟨"month/2026-09.md", some ⟨month, 8⟩,
      ["# Outcomes".toList,
       "- [ ] 5 Lean: through ch.8 of the tutorial ^O1".toList,
       "- [ ] 4 Soundcode: end-to-end demo runs    ^O2".toList]⟩]

set_option maxRecDepth 40000 in
theorem the_rooted_witness_loads : loadsOk rootedWitness = true := by decide

/-- The loaded store.  Total by `the_rooted_witness_loads`: the error branch is refuted, not
defaulted (`Boundary.lookWallPlan`'s pattern, as `storedPlan` does it). -/
def rootedPlan : WfPlan :=
  match h : loadPlan rootedWitness with
  | .ok p => p
  | .error _ => absurd the_rooted_witness_loads (by simp [loadsOk, h])

/-- Two candidates that agree on **every** field but their id, so the key's first two digits
(`wall`, then `p`) tie and the order falls through to the sites — which is where the root walk
lives. -/
def rootedCands : List (Look.Cand × Option Look.Floor) :=
  [(⟨['m','1'], 3, none, 50, none, false, false, false, false, false, false, none, Look.wfUnconstrained⟩, none),
   (⟨['m','2'], 3, none, 50, none, false, false, false, false, false, false, none, Look.wfUnconstrained⟩, none)]

/-- The §4.3 Wednesday with that plan behind it and those two candidates on the wire. -/
def theRootedRequest : PlanReq :=
  { theRequest with plan := rootedPlan, cands := ⟨rootedCands, by decide⟩ }

set_option maxRecDepth 40000 in
/-- **The two orders disagree, computed.**  `^m1` is earlier in the week and its root is later
in the month; `^m2` is the other way.  `Plan.rootOf` is the walk and `PlanReq.rootSite` reads
it — neither is re-implemented here. -/
theorem the_rooted_witness_separates_the_root_from_the_item :
    theRootedRequest.ownSite ['m','1'] = some ⟨0, 1⟩ ∧
      theRootedRequest.rootSite ['m','1'] = some ⟨1, 2⟩ ∧
      theRootedRequest.ownSite ['m','2'] = some ⟨0, 2⟩ ∧
      theRootedRequest.rootSite ['m','2'] = some ⟨1, 1⟩ := by
  decide

set_option maxRecDepth 40000 in
/-- **And §7.2 gives the two the same `p`**, so nothing ahead of the sites can decide the
pair.  Without this the next theorem would be satisfied by a key that never looked at a site
at all. -/
theorem the_rooted_requests_answers_tie_on_p :
    theRootedRequest.candAnswers.map (fun o => (o.out.cand.id, o.out.p))
      = [(['m','1'], some 5), (['m','2'], some 5)] := by
  decide

set_option maxRecDepth 40000 in
/-- **THE ROOT'S LINE ORDER DECIDES, AND THE ITEM'S OWN DOES NOT.**  The candidates arrive as
`^m1, ^m2` and their own line order is `^m1, ^m2`; the produced order is `^m2, ^m1`, because
`^m2`'s root stands first in the month.  Both the request position and the item's own site
would give the other answer, so this is the one witness that separates fork
`((u8, (p, root_order, own_order)), i)` from `((u8, (p, own_order, root_order)), i)`.

**This is the `decide` that the inversion fails** — and the inversion left both suites green
(README gap 677). -/
theorem the_root_order_decides_before_the_items_own :
    rankedIds theRootedRequest = [['m','2'], ['m','1']] ∧
      theRootedRequest.candAnswers.map (fun o => o.out.cand.id) = [['m','1'], ['m','2']] := by
  decide

/-- The same two documents with the **parents exchanged**: `^m1 @O1`, `^m2 @O2`.  Nothing else
moves — not a line, not an id, not a candidate. -/
def rootedWitnessSwapped : List ReqDoc :=
  [⟨"week/2026-W37.md", some ⟨week, 35⟩,
      ["# Tasks".toList,
       "- [ ] 5 6b Finish the report @O1 ^m1".toList,
       "- [ ] 5 6b Write the tests   @O2 ^m2".toList]⟩,
   ⟨"month/2026-09.md", some ⟨month, 8⟩,
      ["# Outcomes".toList,
       "- [ ] 5 Lean: through ch.8 of the tutorial ^O1".toList,
       "- [ ] 4 Soundcode: end-to-end demo runs    ^O2".toList]⟩]

set_option maxRecDepth 40000 in
theorem the_swapped_rooted_witness_loads : loadsOk rootedWitnessSwapped = true := by decide

def rootedPlanSwapped : WfPlan :=
  match h : loadPlan rootedWitnessSwapped with
  | .ok p => p
  | .error _ => absurd the_swapped_rooted_witness_loads (by simp [loadsOk, h])

def theSwappedRootRequest : PlanReq :=
  { theRequest with plan := rootedPlanSwapped, cands := ⟨rootedCands, by decide⟩ }

set_option maxRecDepth 40000 in
/-- **Exchanging the two `@parent`s exchanges the order**, on a wire that did not change: the
perturbation half of the pair above (README gap 577's rule — a wrong *value* must fail, not
only a missing name).  A key that read the item's own site would answer `^m1, ^m2` for **both**
witnesses; §7.4's reads the root and answers differently for each. -/
theorem exchanging_the_parents_exchanges_the_order :
    rankedIds theSwappedRootRequest = [['m','1'], ['m','2']] ∧
      rankedIds theSwappedRootRequest ≠ rankedIds theRootedRequest := by
  decide

set_option maxRecDepth 40000 in
/-- **The census at the day the two lifts are about**, over `theRunningRequest` — the §4.3
Wednesday at 14:00 with `m1` running, which is the request
`PlanCheck.dayPlan_ok_core`'s and `PlanCheck.dayPlan_ok_core_from_now`'s doc comments both
cite.  `the_battery_census_over_a_produced_day` does this at `theStoredRequest`; this does it
at the reserved day, which is the one those two paragraphs were written about.

Reading it, for `checksCore`'s seven over the **whole** day:

* `noOverbook` — **a subject**: `withoutActive` drops both `m1` rows and leaves `m2`'s hour, so
  the sum it compares with the budget is 3 600 s and not 0;
* `oneBlockAtATime` — **a subject**: three Block rows;
* `noBlockOverAWall` — **a subject**: three Blocks beside one Wall;
* `wallsUnmoved` — **a subject**: the one Wall row names `^g1` and this store holds it (which
  is exactly what the store behind `theStoredRequest` does **not** do);
* `energyFilterOk` — **vacuous**: no row carries a slot energy (P5);
* `noBlockOverABreak` — **vacuous**: no Break row (P5, README gap 551);
* `noDemandingAfterWindDown` — **vacuous**: no Block starts at or after the wind-down (P5/P7).

**Four of seven, not six.**  And over the `withoutPast` day the new lift is about, `noOverbook`
joins them: the only surviving Block **is** the Active reservation and `withoutActive` removes
it, which is design §6.3 row 1 taken literally — **three of seven**.

**W-18:** those two numbers are this request's, and one of the three vacuous checkers is
vacuous only here.  `the_battery_census_at_the_census_request` is the same count at
`theCensusRequest`, whose log holds a `break`: **five of seven** over the whole day, **four of
seven** over the `withoutPast` day, and **seven of eleven** over all eleven.  The two that
stay empty there stay empty everywhere, and `PlanCheck`'s vacuity section proves it. -/
theorem the_battery_census_at_the_reserved_day :
    ((dayPlan theRunningRequest).segments.filter
        (fun s => s.val.kind == SegKind.block)).length = 3 ∧
      ((dayPlan theRunningRequest).segments.filter
        (fun s => s.val.kind == SegKind.wall)).map
          (fun s => (s.val.item.bind
            (fun i => theRunningRequest.plan.val.store.get i)).isSome) = [true] ∧
      blockSeconds (PlanCheck.withoutActive theRunningRequest (dayPlan theRunningRequest))
        = 3600 ∧
      (dayPlan theRunningRequest).segments.filter (fun s => s.val.kind == SegKind.brk) = [] ∧
      (dayPlan theRunningRequest).segments.filter (fun s => s.val.energy.isSome) = [] ∧
      (dayPlan theRunningRequest).segments.filter (fun s => s.val.kind == SegKind.block &&
        decide (theRunningRequest.windDownSec ≤ s.val.start)) = [] ∧
      ((PlanCheck.withoutPast theRunningRequest (dayPlan theRunningRequest)).segments.filter
        (fun s => s.val.kind == SegKind.block)).length = 1 ∧
      blockSeconds (PlanCheck.withoutActive theRunningRequest
        (PlanCheck.withoutPast theRunningRequest (dayPlan theRunningRequest))) = 0 ∧
      (PlanCheck.withoutPast theRunningRequest (dayPlan theRunningRequest)).segments.filter
        (fun s => s.val.kind == SegKind.brk) = [] ∧
      (PlanCheck.withoutPast theRunningRequest (dayPlan theRunningRequest)).segments.filter
        (fun s => s.val.energy.isSome) = [] ∧
      (PlanCheck.withoutPast theRunningRequest (dayPlan theRunningRequest)).segments.filter
        (fun s => s.val.kind == SegKind.block &&
          decide (theRunningRequest.windDownSec ≤ s.val.start)) = [] := by
  decide

/-! ############################################################################
## 14. The census, settled: one request, one ratio — stage 6, run W-18, track G

*(Written `## 13.` on branch `w18-g`, where `## 13.` had existed since W-17's repair
step; renumbered to 14 by W-18's land step — README gap 772, W-17 gap 672's class.
Nothing in `check.sh` can see a duplicated Markdown heading inside a doc comment,
which is why it shipped twice.)*
############################################################################

Three numbers for one question stood in this repository at the end of W-17, and they were
measured at three different places: **five of eleven** with a subject over the day at
`theStoredRequest` (`the_battery_census_over_a_produced_day`), **four of seven** over
`checksCore` at `theRunningRequest` (`the_battery_census_at_the_reserved_day`, and
`PlanCheck.lean`'s header), and gap 650's **four** checkers a later step must clear.  None of
them is wrong; together they are not an answer, because a reader cannot tell which population
any of them is about.

This section gives the question one answer, and it has two halves that must not be run
together:

* **a request question** — how much of the battery a witness can make bite.  Answered here
  with **one** request, `theCensusRequest`, and **one** ratio: **seven of the eleven** have a
  subject on the day it produces.  That is up from five, and the two it adds cost no new step:
  `wallsUnmoved` needed a store that holds the wall the day places, and `noBlockOverABreak`
  needed a **log with a `break` in it**.  Gap 650 gave the second to P5, and that was wrong.
* **a step question** — what no witness can reach.  Answered in `PlanCheck.lean`, as four
  theorems about **every** `PlanReq` rather than a population at one: no Block row carries a
  slot energy, no Block row reaches the wind-down, no row is a Batch row, and
  `Diagnostics.impossible` is empty.  Those four are the honest residue, they are P5's and
  P8's, and each is now a build-time wall that the step must delete.

**Seven, then, and four — and the four are proved, not counted.**

`theCensusRequest` is the two existing witnesses joined, with nothing invented: the calendar
document `Boundary.lookWallWitness` already holds, the two ranked tasks `storedWitness`
already holds, the six log lines `witLines` already holds, `theRunningState`'s running block,
and **one** new line of log.  It goes through `mkPlanReq?`, so its wall index really is its
plan's (which is what `theStoredRequest` gives up by swapping the plan behind the builder's
back) and `hagree` comes from `mkPlanReq?_ok_wallsAgree` rather than from a `decide`. -/

/-- **The one new line: a fifteen-minute `break` at 08:05**, between the morning's two blocks,
in the fork's own bytes (`tm/tests/fixtures/fork-4748911-log-lines.jsonl`'s `break` shape:
`planned_min`, and `actual_min`/`where` optional).  `Replay.dayArm` turns it into a day
segment of kind `Replay.SegKind.brk`, and `Planner.pastKind` maps that to `SegKind.brk` — so
the Break row on the day is the log's, exactly as `Planner.a_break_row_is_a_replayed_row`
says every Break row is until P5's `kept_breaks` (README gap 551). -/
def censusBreakLine : Log.Line :=
  ⟨7, some ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','9','T','0','8',':','0','5',':','0','0','-','0','5',':','0','0','"',',','"','e','v','"',':','"','b','r','e','a','k','"',',','"','p','l','a','n','n','e','d','_','m','i','n','"',':','1','5','}']⟩

/-- `witLines` with the break appended — the six lines are **reused**, not respelled. -/
def censusLines : List Log.Line := witLines ++ [censusBreakLine]

set_option maxRecDepth 40000 in
theorem censusRun_resumes_ok : runOk Cal.chicago 739867 censusLines = true := by decide

def censusRun : Seal.Run :=
  match h : Seal.resumeRun Cal.chicago 739867 (Seal.Ckpt.empty Cal.chicago) censusLines with
  | .ok run => run
  | .error _ => absurd censusRun_resumes_ok (by simp [runOk, h])

theorem censusRun_resumes :
    Seal.resumeRun Cal.chicago 739867 (Seal.Ckpt.empty Cal.chicago) censusLines
      = .ok censusRun := by
  unfold censusRun
  split
  · rename_i run h; rw [h]
  · rename_i e h; exact absurd censusRun_resumes_ok (by simp [runOk, h])

/-- **The calendar and the tasks in one plan** — `Boundary.lookWallWitness`' meeting and
`storedWitness`' two ranked siblings, unchanged, in one document list.  Neither is a new
witness and neither line is retyped with a difference. -/
def censusWitness : List ReqDoc :=
  [⟨"calendar/2026-W37.md", none,
     ["- [ ] 3 Meeting w/ host      at:2026-09-09T12:50/13:50 loc:zoom ^g1".toList]⟩,
   ⟨"week/2026-W37.md", some ⟨week, 35⟩,
      ["# Tasks".toList, "- [ ] 5 6b Finish the report ^m1 hot".toList,
       "- [ ] 5 6b Write the tests ^m2".toList]⟩,
   ⟨"month/2026-09.md", some ⟨month, 8⟩, ["# Outcomes".toList]⟩]

set_option maxRecDepth 40000 in
theorem the_census_witness_loads : loadsOk censusWitness = true := by decide

def censusPlan : WfPlan :=
  match h : loadPlan censusWitness with
  | .ok p => p
  | .error _ => absurd the_census_witness_loads (by simp [loadsOk, h])

theorem censusPlan_loads : loadPlan censusWitness = .ok censusPlan := by
  unfold censusPlan
  split
  · rename_i p h; rw [h]
  · rename_i e h; exact absurd the_census_witness_loads (by simp [loadsOk, h])

set_option maxRecDepth 40000 in
/-- **Adding the tasks moves no wall.**  The two task lines carry no `at:`, so the combined
plan's wall index is the calendar's alone — which is what lets the builder accept this request
against `witInputIn`'s `Look.wednesdayWall` and what makes `wallsAgree` true here.  (It is
false at `theStoredRequest`, which swapped the plan for one with no wall in it.) -/
theorem the_census_witness_indexes_the_calendars_one_wall :
    Look.wallIndex Cal.chicago 60 censusPlan.val = Look.wednesdayWall := by decide

set_option maxRecDepth 8000 in
/-- **What the store holds, computed**: the calendar's meeting at §3.1's default `ci` of three,
and the morning's two tasks at `ci:5`, two ranked siblings of one document with `hot` on the
first — the three facts the seven non-vacuous checkers turn on. -/
theorem the_census_witness_holds_the_wall_and_two_ranked_siblings :
    censusPlan.val.store.dom = [['m','2'], ['m','1'], ['g','1']] ∧
      (effectiveCi censusPlan.val ['m','1']).val = 5 ∧
      (effectiveCi censusPlan.val ['m','2']).val = 5 ∧
      (effectiveCi censusPlan.val ['g','1']).val = 3 ∧
      rootPrio censusPlan.val ['m','1'] = rootPrio censusPlan.val ['m','2'] ∧
      (censusPlan.val.store.get ['m','1']).map (fun e => (e.val.live.doc, e.val.live.rank,
          e.val.flags)) = some (1, 1, [Field.Flag.hot]) ∧
      (censusPlan.val.store.get ['m','2']).map (fun e => (e.val.live.doc, e.val.live.rank,
          e.val.flags)) = some (1, 2, []) := by
  decide

def witReqInCensus : PlanReqIn :=
  { witReqIn with docs := censusWitness, lines := censusLines, state := theRunningState }

/-- **The census request**: the §4.3 Wednesday at 14:00, `m1` running, a store that holds both
the calendar's wall and the morning's two tasks, and a log that holds a break. -/
def theCensusRequest : PlanReq :=
  ⟨censusPlan, censusRun, witInput, theRunningState, Capped.nil, witPrio, Capped.nil, none⟩

/-- **The builder accepts it** — by rewriting with the four stage equations, never by a
`decide` that holds the load, the resume and the lookahead at once. -/
theorem witBuildsCensus : mkPlanReq? witReqInCensus = .ok theCensusRequest := by
  obtain ⟨ht, hz, hd, hw, -⟩ := witInput_fields
  unfold mkPlanReq? witReqInCensus witReqIn theCensusRequest
  simp only [censusPlan_loads, witInput_decodes]
  rw [if_neg (by
    rw [hw, hz, hd]
    simp only [Look.DayCfg.shipped, Look.CutCfg.shipped, ne_eq]
    exact not_not_intro the_census_witness_indexes_the_calendars_one_wall.symm)]
  rw [hz, ht, censusRun_resumes]
  simp only [Capped.ofList?_nil, mkRoutines?_of_none]

/-- `hagree`, from the builder and not from a `decide` — and **true here**, where the two
earlier census requests split it between them. -/
theorem theCensusRequest_wallsAgree : theCensusRequest.wallsAgree = true :=
  mkPlanReq?_ok_wallsAgree witReqInCensus theCensusRequest witBuildsCensus

/-- `hactive` and `hday`, the two R10 hypotheses both lifts carry. -/
theorem the_census_request_agrees :
    theCensusRequest.activeAgrees = true ∧ theCensusRequest.dayAgrees = true := by decide

/-- `hnowcal`: the instant being planned is inside the calendar. -/
theorem the_census_request_is_inside_the_calendar :
    theCensusRequest.now.sec + 1 < LogStamp.yearEnd := by decide

set_option maxRecDepth 40000 in
/-- **The day, end to end**: the morning's two Blocks with the **break between them**, the
written wall, §8.2 choice 5b's reservation and §16's two evening rows — seven rows, in the
fork's row order.  The Break row is the only thing here that was not already computed at
`theRunningRequest`, and it is the row gap 650 said no request could produce before P5. -/
theorem the_census_day_carries_the_mornings_break :
    (dayPlan theCensusRequest).segments.map
        (fun s => (s.val.start, s.val.stop, s.val.kind, s.val.item))
      = [((Cal.instantOf Cal.chicago 739867 425).sec, (Cal.instantOf Cal.chicago 739867 485).sec,
          SegKind.block, some (['m','1'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 485).sec, (Cal.instantOf Cal.chicago 739867 500).sec,
          SegKind.brk, none),
         ((Cal.instantOf Cal.chicago 739867 545).sec, (Cal.instantOf Cal.chicago 739867 605).sec,
          SegKind.block, some (['m','2'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 770).sec, (Cal.instantOf Cal.chicago 739867 830).sec,
          SegKind.wall, some (['g','1'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 840).sec, (Cal.instantOf Cal.chicago 739867 880).sec,
          SegKind.block, some (['m','1'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 1290).sec,
          (Cal.instantOf Cal.chicago 739867 1320).sec, SegKind.windDown, none),
         ((Cal.instantOf Cal.chicago 739867 1320).sec, (Cal.instantOf Cal.chicago 739868 0).sec,
          SegKind.sleep, none)] := by
  decide

set_option maxRecDepth 40000 in
/-- **The battery's verdict on that day**: all eleven pass. -/
theorem the_battery_passes_at_the_census_request :
    PlanCheck.planOk permissive theCensusRequest (dayPlan theCensusRequest) = true := by
  decide

set_option maxRecDepth 40000 in
/-- **THE RATIO: seven of eleven have a subject on this day; four do not.**  Every line below
is a population, computed, and the two tables in this module's section 11 are its history.

| checker | subject here | why |
|---|---|---|
| `noOverbook` | **yes** | `withoutActive` leaves `m2`'s hour: 3 600 s against the budget |
| `oneBlockAtATime` | **yes** | three Block rows |
| `noBlockOverAWall` | **yes** | three Blocks beside one Wall |
| `noBlockOverABreak` | **yes** | three Blocks beside **one Break row** — the log's, new here |
| `wallsUnmoved` | **yes** | the Wall row names `^g1` and **this** store holds it |
| `monotoneInRank` | **yes** | `m1`/`m2`: one document, ranks 1 and 2, both `ci:5`, equal `rootPrio`, both assigned |
| `hotBeforeQueue` | **yes** | `m1` carries `hot`, `m2` does not, both assigned |
| `energyFilterOk` | **no** | no Block row carries a slot energy — **and none can**, `PlanCheck.no_block_row_of_the_day_carries_a_slot_energy` (P5) |
| `noDemandingAfterWindDown` | **no** | no Block row reaches the wind-down — **and none can**, `PlanCheck.no_block_row_of_the_day_reaches_the_wind_down` (P5/P7) |
| `batchDoesNotReachPast` | **no** | no Batch row — **and none can**, `PlanCheck.the_day_has_no_batch_row` (P5) |
| `impossibleKept` | **no** | `Diagnostics.impossible` is empty — **and always is**, `PlanCheck.the_day_names_no_impossible_item` (P8) |

The last four conjuncts below are the *populations* at this request; the theorems named beside
them are the general statements, which is the distinction this section exists to draw.  The
Break row is computed **twice** — once on the whole day and once on `PlanCheck.withoutPast`'s
day — because `SegKind.isWork` is false of a Break, so the row survives the restriction and
`noBlockOverABreak` has a subject in the day *both* lifts are about. -/
theorem the_battery_census_at_the_census_request :
    ((dayPlan theCensusRequest).segments.filter
        (fun s => s.val.kind == SegKind.block)).length = 3 ∧
      blockSeconds (PlanCheck.withoutActive theCensusRequest (dayPlan theCensusRequest))
        = 3600 ∧
      ((dayPlan theCensusRequest).segments.filter
        (fun s => s.val.kind == SegKind.wall)).map
          (fun s => (s.val.item.bind
            (fun i => theCensusRequest.plan.val.store.get i)).isSome) = [true] ∧
      ((dayPlan theCensusRequest).segments.filter
        (fun s => s.val.kind == SegKind.brk)).length = 1 ∧
      ((PlanCheck.withoutPast theCensusRequest (dayPlan theCensusRequest)).segments.filter
        (fun s => s.val.kind == SegKind.brk)).length = 1 ∧
      ((PlanCheck.withoutPast theCensusRequest (dayPlan theCensusRequest)).segments.filter
        (fun s => s.val.kind == SegKind.block)).length = 1 ∧
      assignedOf (dayPlan theCensusRequest) = [['m','1'], ['m','2'], ['m','1']] ∧
      assignedFrom (dayPlan theCensusRequest) theCensusRequest.now.sec = [['m','1']] ∧
      (dayPlan theCensusRequest).segments.filter (fun s => s.val.energy.isSome) = [] ∧
      (dayPlan theCensusRequest).segments.filter (fun s => s.val.kind == SegKind.block &&
        decide (theCensusRequest.windDownSec ≤ s.val.start)) = [] ∧
      (dayPlan theCensusRequest).diagnostics.impossible.val = [] := by
  decide

/-- **The new lift, fired at the census request.**  Every hypothesis of
`PlanCheck.dayPlan_ok_core_from_now` is supplied by a theorem above; nothing here is a
`decide`.  `the_running_request_is_plain`'s argument does not carry over — this store holds
three ids, not one — so `hplain` is re-proved below at this request. -/
theorem the_census_request_is_plain :
    ∀ (i : Id) (e : Entity) (a b : Field.DT),
      theCensusRequest.plan.val.store.get i = some e →
      e.val.shape = Field.Shape.interval a b →
      e.val.buffer = none ∧
        theCensusRequest.dayStart ≤ (Cal.instantOf theCensusRequest.tz a.day a.time).sec ∧
        (Cal.instantOf theCensusRequest.tz b.day b.time).sec ≤ theCensusRequest.dayEnd ∧
        (Cal.instantOf theCensusRequest.tz a.day a.time).sec
          < (Cal.instantOf theCensusRequest.tz b.day b.time).sec ∧
        (Cal.instantOf theCensusRequest.tz b.day b.time).sec < LogStamp.yearEnd := by
  intro i e a b hget0 hsh
  have hget : censusPlan.val.store.get i = some e := hget0
  have hmem : i ∈ censusPlan.val.store.dom := PlanCheck.mem_dom_of_get _ i e hget
  rw [the_census_witness_holds_the_wall_and_two_ranked_siblings.1] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · have h2 : (censusPlan.val.store.get ['m','2']).map (fun x => x.val.shape)
        = some Field.Shape.none := by decide
    rw [hget, Option.map_some] at h2
    exact absurd ((Option.some.inj h2).symm.trans hsh) (by simp)
  · have h1 : (censusPlan.val.store.get ['m','1']).map (fun x => x.val.shape)
        = some Field.Shape.none := by decide
    rw [hget, Option.map_some] at h1
    exact absurd ((Option.some.inj h1).symm.trans hsh) (by simp)
  · have hg : (censusPlan.val.store.get ['g','1']).map (fun x => (x.val.shape, x.val.buffer))
        = some (Field.Shape.interval ⟨739867, ⟨770, by decide⟩⟩ ⟨739867, ⟨830, by decide⟩⟩,
                none) := by decide
    rw [hget, Option.map_some] at hg
    have he := Option.some.inj hg
    have hsh0 : e.val.shape
        = Field.Shape.interval ⟨739867, ⟨770, by decide⟩⟩ ⟨739867, ⟨830, by decide⟩⟩ :=
      congrArg Prod.fst he
    have hbuf : e.val.buffer = none := congrArg Prod.snd he
    rw [hsh0] at hsh
    injection hsh with ha hb
    subst ha
    subst hb
    exact ⟨hbuf, by decide, by decide, by decide, by decide⟩

theorem the_lift_applies_at_the_census_request :
    PlanCheck.planOkCore theCensusRequest
      (PlanCheck.withoutPast theCensusRequest (dayPlan theCensusRequest)) = true :=
  PlanCheck.dayPlan_ok_core_from_now theCensusRequest theCensusRequest_wallsAgree
    the_census_request_agrees.1 the_census_request_agrees.2
    the_census_request_is_inside_the_calendar the_census_request_is_plain

/-! ### The refutation: a break the log holds **inside** a block the log holds

`Goals.plan_places_no_block_over_a_break` quantifies over **every** Block row and **every**
Break row of the day.  Both come from the replay (`Planner.a_break_row_is_a_replayed_row`, and
`PlanCheck.dayPlan_block_rows_are_replayed_or_reserved`), so a log that records a `break` while
a block is running gives the day a Break row **inside** a Block row, and neither of them is the
planner's doing.  That is finding 1 (README gap 385) for the third time: step P3 took it for
E1, W-17 for the wall law, and this is the third.

The witness is the census log with its one break **moved** from 08:05 to 07:30 — nothing else
changes, and the six original lines are still `witLines`, renumbered by one rather than
respelled. -/

def midBreakLine : Log.Line :=
  ⟨4, some ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','9','T','0','7',':','3','0',':','0','0','-','0','5',':','0','0','"',',','"','e','v','"',':','"','b','r','e','a','k','"',',','"','p','l','a','n','n','e','d','_','m','i','n','"',':','1','5','}']⟩

/-- `witLines` with the break spliced in after the `start` of `m1` and the rest renumbered —
`Log.contiguousFrom`'s numbering, kept. -/
def midBreakLines : List Log.Line :=
  witLines.take 3 ++ [midBreakLine] ++ (witLines.drop 3).map (fun l => ⟨l.n + 1, l.text⟩)

set_option maxRecDepth 40000 in
theorem midBreakRun_resumes_ok : runOk Cal.chicago 739867 midBreakLines = true := by decide

def midBreakRun : Seal.Run :=
  match h : Seal.resumeRun Cal.chicago 739867 (Seal.Ckpt.empty Cal.chicago) midBreakLines with
  | .ok run => run
  | .error _ => absurd midBreakRun_resumes_ok (by simp [runOk, h])

/-- The census request with that log behind it, and nothing else changed. -/
def theMidBreakRequest : PlanReq := { theCensusRequest with run := midBreakRun }

set_option maxRecDepth 40000 in
/-- **The day lays a Block across a Break**, computed: `m1`'s replayed block runs 07:05-08:05
and the break the log records runs 07:30-07:45, inside it.  Both halves are here — the
overlapping pair, **and** `PlanCheck.noBlockOverABreak`'s own verdict on the day, which is the
battery's opinion and not a restatement of a `Planner` theorem. -/
theorem the_mid_break_day_lays_a_block_across_a_break :
    (dayPlan theMidBreakRequest).segments.map
        (fun s => (s.val.start, s.val.stop, s.val.kind))
      = [((Cal.instantOf Cal.chicago 739867 425).sec, (Cal.instantOf Cal.chicago 739867 485).sec,
          SegKind.block),
         ((Cal.instantOf Cal.chicago 739867 450).sec, (Cal.instantOf Cal.chicago 739867 465).sec,
          SegKind.brk),
         ((Cal.instantOf Cal.chicago 739867 545).sec, (Cal.instantOf Cal.chicago 739867 605).sec,
          SegKind.block),
         ((Cal.instantOf Cal.chicago 739867 770).sec, (Cal.instantOf Cal.chicago 739867 830).sec,
          SegKind.wall),
         ((Cal.instantOf Cal.chicago 739867 840).sec, (Cal.instantOf Cal.chicago 739867 880).sec,
          SegKind.block),
         ((Cal.instantOf Cal.chicago 739867 1290).sec,
          (Cal.instantOf Cal.chicago 739867 1320).sec, SegKind.windDown),
         ((Cal.instantOf Cal.chicago 739867 1320).sec, (Cal.instantOf Cal.chicago 739868 0).sec,
          SegKind.sleep)] ∧
      PlanCheck.noBlockOverABreak theMidBreakRequest (dayPlan theMidBreakRequest) = false ∧
      PlanCheck.planOkCore theMidBreakRequest (dayPlan theMidBreakRequest) = false := by
  decide

set_option maxRecDepth 40000 in
/-- **`Goals.plan_places_no_block_over_a_break` is FALSE as stage 6 wrote it** (AGENTS §3.1
item 3, D5).  The goal leaves `Goals.lean` with this beside it and
`PlanCheck.plan_places_no_block_over_a_break` — the same law over the Block rows that start at
or after `now` — proved in the same commit. -/
theorem plan_places_no_block_over_a_break_as_stage_6_wrote_it_is_refuted :
    ¬ (∀ (r : PlanReq) (b k : WfSeg), b ∈ (dayPlan r).segments → k ∈ (dayPlan r).segments →
        b.val.kind = SegKind.block → k.val.kind = SegKind.brk →
        b.val.stop ≤ k.val.start ∨ k.val.stop ≤ b.val.start) := by
  intro h
  have hbad : PlanCheck.noBlockOverABreak theMidBreakRequest (dayPlan theMidBreakRequest)
      = false := the_mid_break_day_lays_a_block_across_a_break.2.1
  have hok : PlanCheck.noBlockOverABreak theMidBreakRequest (dayPlan theMidBreakRequest)
      = true :=
    (PlanCheck.noBlockOverABreak_iff theMidBreakRequest _).mpr
      (fun b hb k hk hbk hkk => h theMidBreakRequest b k hb hk hbk hkk)
  rw [hok] at hbad
  exact absurd hbad (by simp)

/-- **The restated law is not vacuous at the census request**: choice 5b's reservation is a
Block row starting at `now`, the morning's break is a Break row, and
`PlanCheck.plan_places_no_block_over_a_break` really does compare them.  Applied, not
admired. -/
theorem the_break_law_applies_at_the_census_request (b k : WfSeg)
    (hb : b ∈ (dayPlan theCensusRequest).segments)
    (hk : k ∈ (dayPlan theCensusRequest).segments)
    (hbk : b.val.kind = SegKind.block) (hkk : k.val.kind = SegKind.brk)
    (hnow : theCensusRequest.now.sec ≤ b.val.start) :
    b.val.stop ≤ k.val.start ∨ k.val.stop ≤ b.val.start :=
  PlanCheck.plan_places_no_block_over_a_break theCensusRequest
    the_census_request_is_inside_the_calendar b k hb hk hbk hkk hnow

/-! ############################################################################
## 15. §8.2 step 5's groups, run rather than argued (stage 6 step P5b, AGENTS §5.2)

Every law in `Planner.lean`'s group section is a `∀` over a request.  The witnesses below are
`decide` over one, and each is built so that **the component it is about is the only thing that
differs** — W-17's lesson, which cost P4 a sort key whose two halves could be swapped with 1,342
tests green.  Six components: the gather's `continue` on a different `ci`, its `break` on an
equal one, the `maxBatch` room, the split's three key parts, the `max:` commit, and the group
sort.
############################################################################ -/

/-- The nine, with `planned_min` and `loc:` set — the two facts §8.2 step 5's grouping reads. -/
def planFacts (pm : Nat) (l : Field.Loc) : Look.PlanFacts :=
  { Look.PlanFacts.unconstrained with plannedMin := pm, loc := l }

def wfPlanFacts (pm : Nat) (l : Field.Loc) (h : Look.PlanFacts.wf (planFacts pm l) = true) :
    Look.WfPlanFacts := ⟨planFacts pm l, h⟩

/-- One batching candidate: no due (so §7.3's pass does not enter it), a written `!1` so every
one of the six answers `p = 3` and the order is the request's, and the two grouping facts. -/
def bCand (id : List Char) (ci : Fin 6) (pm : Nat) (l : Field.Loc)
    (h : Look.PlanFacts.wf (planFacts pm l) = true) : Look.Cand × Option Look.Floor :=
  (⟨id, ci, some 0, 10, none, false, false, false, false, false, false, none,
     wfPlanFacts pm l h⟩, none)

/-- **Six candidates aimed at §7.5's two rules.**  `blockMin` is 60 and `batch_max_min` 20, so
every one of the six is *gatherable* and only the planned minutes and the `ci` decide.

`^b1` (10m) leads; `^b2` (20m) joins; `^b3` is `ci 2` and is **passed over**; `^b4` (40m) is
`ci 3` and would take the batch to 70 > 60, so it **stops** the gather; `^b5` (5m) is `ci 3`
and *would* have fitted — it is the candidate a gather without the `break` would have reached
past, which is §8.3's monotone-rank rule and E2's whole content; `^b6` is `ci 2` again.
`^b2` carries `loc:out` where the rest carry none, which is what the split reads. -/
def witBatchCands : List (Look.Cand × Option Look.Floor) :=
  [bCand ['b','1'] 3 10 .any  (by decide),
   bCand ['b','2'] 3 20 .out  (by decide),
   bCand ['b','3'] 2 10 .any  (by decide),
   bCand ['b','4'] 3 40 .any  (by decide),
   bCand ['b','5'] 3 5  .any  (by decide),
   bCand ['b','6'] 2 10 .any  (by decide)]

def theBatchRequest : PlanReq := { theRequest with cands := ⟨witBatchCands, by decide⟩ }

/-- The ids of each batch §7.5 gathered, in the order the fold walks them. -/
def batchIds (r : PlanReq) : List (List Id) :=
  r.dayBatches.map (fun b => b.map (fun x => x.cand.id))

/-- The ids of each group `build_groups` built, with the minutes it commits to. -/
def groupIds (r : PlanReq) : List (List Id) :=
  r.buildGroups.map (fun g => g.members.map (fun x => x.cand.id))

def groupCommits (r : PlanReq) : List Nat := r.buildGroups.map Group.commitMin

/-- The same six with a `max:` on `^b4`: sixty minutes capped, `d` of them already spent. -/
def bCandCap (id : List Char) (ci : Fin 6) (pm : Nat) (d : Nat)
    (h : Look.PlanFacts.wf { planFacts pm .any with cap := some ⟨60, d⟩ } = true) :
    Look.Cand × Option Look.Floor :=
  (⟨id, ci, some 0, 10, none, false, false, false, false, false, false, none,
     ⟨{ planFacts pm .any with cap := some ⟨60, d⟩ }, h⟩⟩, none)

/-- `^b4` with forty of its sixty capped minutes spent — twenty left, which is **less** than
the forty-five its group's estimates ask for. -/
def witCapCands : List (Look.Cand × Option Look.Floor) :=
  [bCand ['b','1'] 3 10 .any (by decide), bCand ['b','2'] 3 20 .out (by decide),
   bCand ['b','3'] 2 10 .any (by decide), bCandCap ['b','4'] 3 40 40 (by decide),
   bCand ['b','5'] 3 5 .any (by decide), bCand ['b','6'] 2 10 .any (by decide)]

/-- The same `max:` with **nothing** spent — sixty left, which binds nothing. -/
def witCapSlackCands : List (Look.Cand × Option Look.Floor) :=
  [bCand ['b','1'] 3 10 .any (by decide), bCand ['b','2'] 3 20 .out (by decide),
   bCand ['b','3'] 2 10 .any (by decide), bCandCap ['b','4'] 3 40 0 (by decide),
   bCand ['b','5'] 3 5 .any (by decide), bCand ['b','6'] 2 10 .any (by decide)]

def theCapRequest : PlanReq := { theRequest with cands := ⟨witCapCands, by decide⟩ }
def theCapSlackRequest : PlanReq := { theRequest with cands := ⟨witCapSlackCands, by decide⟩ }

/-- The six with `^b5` made `atomic`, and nothing else. -/
def witAtomicCands : List (Look.Cand × Option Look.Floor) :=
  [bCand ['b','1'] 3 10 .any (by decide), bCand ['b','2'] 3 20 .out (by decide),
   bCand ['b','3'] 2 10 .any (by decide), bCand ['b','4'] 3 40 .any (by decide),
   (⟨['b','5'], 3, some 0, 10, none, false, false, false, false, false, false, none,
      ⟨{ planFacts 5 .any with splittable := false }, by decide⟩⟩, none),
   bCand ['b','6'] 2 10 .any (by decide)]

def theAtomicRequest : PlanReq := { theRequest with cands := ⟨witAtomicCands, by decide⟩ }

/-- The six with `^b4` renamed to `m1` — §9's running item, so that one request can differ from
another in `state` alone. -/
def witRunBatchCands : List (Look.Cand × Option Look.Floor) :=
  [bCand ['b','1'] 3 10 .any (by decide), bCand ['b','2'] 3 20 .out (by decide),
   bCand ['b','3'] 2 10 .any (by decide), bCand ['m','1'] 3 40 .any (by decide),
   bCand ['b','5'] 3 5 .any (by decide), bCand ['b','6'] 2 10 .any (by decide)]

def theIdleBatchRequest : PlanReq := { theRequest with cands := ⟨witRunBatchCands, by decide⟩ }

def theRunBatchRequest : PlanReq :=
  { theRequest with cands := ⟨witRunBatchCands, by decide⟩, state := theRunningState }

/-- Twenty candidates that plan **nothing** — `round(est × multiplier)` is `0` for a small
enough multiplier (fork `energy::planned_minutes`), so `total_min + 0 ≤ block_min` never fires
and the fork's gather has no bound at all.  This is gap 800's own witness. -/
def witZeroCands : List (Look.Cand × Option Look.Floor) :=
  List.replicate 20 (bCand ['z'] 3 0 .any (by decide))

def theZeroRequest : PlanReq := { theRequest with cands := ⟨witZeroCands, by decide⟩ }

def groupSpents (r : PlanReq) : List (List Id × Nat) :=
  r.startGroups.map (fun g => (g.members.map (fun x => x.cand.id), g.spent))

/-- **The six rank in request order**, so nothing below is about §7.4: they answer one `p`, none
is in the plan, and the tie falls through to the request position. -/
theorem the_batch_request_is_ordered :
    rankedIds theBatchRequest =
      [['b','1'], ['b','2'], ['b','3'], ['b','4'], ['b','5'], ['b','6']] := by decide

/-- **§7.5's two rules, computed.**  `^b1` gathers `^b2` (10 + 20 ≤ 60); `^b3` is another `ci`
and is **passed over**, not a stop — which is why `^b3` later leads a batch of its own that
reaches *past* `^b4` and `^b5` to gather `^b6`; and `^b4` would take `^b1`'s batch to 70, so it
**stops** the walk and `^b5` is left behind although 10 + 20 + 5 = 35 would have fitted.

**`^b5` is the whole of E2**: a gather that treated a candidate that cannot join as a `continue`
rather than a `break` would put it in `^b1`'s batch, and the day would look correct — the batch
prints fine and `^b4`, which ranks ahead of `^b5`, simply never appears.  That is the shipped
bug this law is named after. -/
theorem the_gather_passes_over_another_ci_and_stops_at_its_own :
    batchIds theBatchRequest =
      [[['b','1'], ['b','2']], [['b','3'], ['b','6']], [['b','4'], ['b','5']]] := by decide

/-- **And the split cuts `^b1`'s batch in two on `loc:` alone** — `^b2` carries `loc:out`, every
other fact of the two is equal, and the errand does not ride into the lounge on `^b1`'s block.
The groups `^b3` and `^b4` lead are untouched, so the cut is the key's and not the split's
existence. -/
theorem the_split_cuts_a_batch_on_its_location :
    groupIds theBatchRequest =
      [[['b','1']], [['b','2']], [['b','3'], ['b','6']], [['b','4'], ['b','5']]] := by decide

/-- **`atomic` cuts on its own**: the same six with `^b5`'s `splittable` cleared and **nothing
else** — `^b4` and `^b5` stop sharing a block, and `^b1`/`^b2`'s cut does not move.  A split
that read one of the two keys for the other would pass one of these two theorems and fail the
other. -/
theorem the_split_cuts_a_batch_on_atomic :
    groupIds theAtomicRequest =
      [[['b','1']], [['b','2']], [['b','3'], ['b','6']], [['b','4']], [['b','5']]] := by decide

set_option maxRecDepth 40000 in
/-- **And §9's running item is cut out of its batch by the *state* alone.**  These two requests
carry the identical candidate list; they differ in `state.active` and in nothing else.  Idle,
`m1` and `^b5` share a block; running, the minutes `m1`'s block still needs are its own. -/
theorem the_split_cuts_out_the_running_block :
    groupIds theIdleBatchRequest =
      [[['b','1']], [['b','2']], [['b','3'], ['b','6']], [['m','1'], ['b','5']]] ∧
    groupIds theRunBatchRequest =
      [[['b','1']], [['b','2']], [['b','3'], ['b','6']], [['m','1']], [['b','5']]] := by decide

set_option maxRecDepth 40000 in
/-- **The reservation's minutes are spent against its own group before the cursor starts** —
fork `groups[gi].left_min -= run.minutes()`.  Forty is the reservation's own length
(`the_reservation_is_clipped_to_the_block_it_is_in`), and it is charged to `m1`'s group and to
no other. -/
theorem the_running_block_starts_its_group_with_its_minutes_spent :
    groupSpents theRunBatchRequest =
      [([['b','1']], 0), ([['b','2']], 0), ([['b','3'], ['b','6']], 0),
       ([['m','1']], 40), ([['b','5']], 0)] := by decide

/-- **§6.2's `max:` binds the commitment, and it binds it by its two numbers.**  The two requests
below carry the same `max: 60` on `^b4`; in the first forty of the sixty are spent, leaving
twenty, and the group commits **twenty** where its estimates ask for forty-five.  In the second
*nothing* is spent, sixty are left, and the same cap binds nothing — so the theorem is about
`cap_left_min()` and not about the presence of a cap. -/
theorem the_commitment_is_capped_by_a_members_max :
    groupCommits theCapRequest = [10, 20, 20, 20] ∧
    groupCommits theCapSlackRequest = [10, 20, 20, 45] := by decide

/-- **The gather stops at `maxBatch`, and the fork's does not** (README gap 800).  Twenty
candidates that plan zero minutes each: `total_min + 0 ≤ block_min` never fires, so the fork's
loop would gather all twenty into one `SegKind::Batch`; `BatchIds` is bounded at sixteen (R10)
and the seventeenth leads a batch of its own.  Nothing is lost — the four are still assigned —
and this is the one behaviour this step deviates in. -/
theorem the_gather_stops_at_the_batch_bound :
    (batchIds theZeroRequest).map List.length = [16, 4] := by decide

/-! ### `Ranked.gatherable`'s five clauses, each refuted on its own (W-19's repair step)

**The predicate fork `batches` calls `small` was entirely unwitnessed in the refusing
direction.**  Replacing the whole of `Planner.Ranked.gatherable`'s body with `:= true` left
`lake build TmKernel:static` green at 168/168 jobs and `check.sh` 8/8 — every theorem in
`Planner.lean` and every one of P5b's nineteen `decide` witnesses included — and each of its
three conjuncts dropped green on its own as well.  Only `:= false` was caught.  That is README
gap 577's class a third time, and it is exactly where P5b's own gap 805 item 4 sends an
auditor: *"a step that wants a behaviour-only inversion of the gather should mutate a reader
(`Ranked.facts`, `Ranked.gatherable`) rather than the loop."*  README gap 875.

What was missing is not a law but a **subject**: every candidate of every witness in this file
was gatherable, so the predicate ranged over nothing that could say `false`.  The six requests
below are three candidates each, differing in **one field of `^t2`** and in nothing else, and
between them they pin all five clauses at the fold's own answer.

*(One honest caveat, said here rather than left for an auditor: `optional` is read by §7's pass
as well — it answers `p = 5` where the other two answer `3` — so `theGatherOptionalRequest`'s
`^t2` also moves to the **end** of the order.  `the_gather_reads_each_of_its_five_clauses`
records that movement rather than hiding it, and the batching answer is still the gather's: a
`gatherable` that dropped `!optional` puts `^t2` back into `^t1`'s batch at its new position,
which is a different list from the one stated.  `wall` moves `^t2` the other way, to the front,
for the same reason — `CandKey.notWall` is the key's first number.)* -/

/-- The nine facts of a gather candidate.  `wall_today` moves with `wall` so that a wall stays
in the **order** (`Planner.entersTheOrder`, `PlanReq.another_days_wall_is_not_ranked`): what is
under test here is the gather's refusal, not the filter's. -/
def gatherFacts (w : Bool) : Look.PlanFacts := { planFacts 10 .any with wallToday := w }

/-- One gather candidate, with the four `Look.Cand` fields `Ranked.gatherable` reads exposed and
every other field of `bCand`'s shape held fixed. -/
def gCand (id : List Char) (rem : Nat) (w o win : Bool)
    (h : Look.PlanFacts.wf (gatherFacts w) = true) : Look.Cand × Option Look.Floor :=
  (⟨id, 3, some 0, rem, none, win, w, o, false, false, false, none, ⟨gatherFacts w, h⟩⟩, none)

def gPlain (id : List Char) : Look.Cand × Option Look.Floor :=
  gCand id 10 false false false (by decide)

/-- `^t1` and `^t3` are the same in all six requests; only `^t2` moves. -/
def gatherTriple (c : Look.Cand × Option Look.Floor) : List (Look.Cand × Option Look.Floor) :=
  [gPlain ['t','1'], c, gPlain ['t','3']]

/-- Three gatherable candidates: one batch. -/
def theGatherRequest : PlanReq :=
  { theRequest with cands := ⟨gatherTriple (gPlain ['t','2']), by decide⟩ }

/-- `^t2` with **nothing left to do** — fork `small`'s `remaining_min > 0`. -/
def theGatherZeroRequest : PlanReq :=
  { theRequest with cands := ⟨gatherTriple (gCand ['t','2'] 0 false false false (by decide)),
                              by decide⟩ }

/-- `^t2` asking for twenty-five minutes against a `batch_max_min` of twenty — too big to share
a block, and the only candidate in this file that is. -/
def theGatherBigRequest : PlanReq :=
  { theRequest with cands := ⟨gatherTriple (gCand ['t','2'] 25 false false false (by decide)),
                              by decide⟩ }

/-- `^t2` as a wall: an Interval, which is placed as itself and never shares. -/
def theGatherWallRequest : PlanReq :=
  { theRequest with cands := ⟨gatherTriple (gCand ['t','2'] 10 true false false (by decide)),
                              by decide⟩ }

/-- `^t2` optional: §16's rest-filler, which takes what is left rather than a share of a block. -/
def theGatherOptionalRequest : PlanReq :=
  { theRequest with cands := ⟨gatherTriple (gCand ['t','2'] 10 false true false (by decide)),
                              by decide⟩ }

/-- `^t2` with a placement window: it is placed inside its own window and nowhere else. -/
def theGatherWindowRequest : PlanReq :=
  { theRequest with cands := ⟨gatherTriple (gCand ['t','2'] 10 false false true (by decide)),
                              by decide⟩ }

/-- `Ranked.gatherable`'s own answer for each entry of the order, at this request's
`batch_max_min`. -/
def gatherFlags (r : PlanReq) : List (Id × Bool) :=
  r.rankedCands.map (fun x => (x.cand.id, x.gatherable r.prio.batchMaxMin))

/-- **The predicate answers `false` for each of the five clauses, and `true` when none bites.**
This is the reader-level half: it fails on `:= true`, on `:= false`, and on the removal of any
one of the three conjuncts — the last because the `remaining` clauses and the three flags are
witnessed by different rows of the same list. -/
theorem the_gather_predicate_refuses_on_each_clause :
    gatherFlags theGatherRequest =
      [(['t','1'], true), (['t','2'], true), (['t','3'], true)] ∧
    gatherFlags theGatherZeroRequest =
      [(['t','1'], true), (['t','2'], false), (['t','3'], true)] ∧
    gatherFlags theGatherBigRequest =
      [(['t','1'], true), (['t','2'], false), (['t','3'], true)] ∧
    gatherFlags theGatherWallRequest =
      [(['t','2'], false), (['t','1'], true), (['t','3'], true)] ∧
    gatherFlags theGatherOptionalRequest =
      [(['t','1'], true), (['t','3'], true), (['t','2'], false)] ∧
    gatherFlags theGatherWindowRequest =
      [(['t','1'], true), (['t','2'], false), (['t','3'], true)] := by decide

/-- **And the refusal reaches the batches**, which is the half a reader-level theorem cannot
give: gathering consumes `room` and `tot`, so a candidate wrongly gathered changes which later
members are gathered, which groups exist, `commitOf`, and every answer of the cursor.

Three gatherable candidates are **one** batch.  Each of the five clauses cuts that batch: the
gather stops at `^t2` (fork `break`) and `^t2` then leads a batch of its own.  Every one of
these six lists changes under `Ranked.gatherable := true`; each of the last five changes under
the removal of its own clause alone, and `theGatherRequest`'s changes under `:= false`. -/
theorem the_gather_reads_each_of_its_five_clauses :
    batchIds theGatherRequest = [[['t','1'], ['t','2'], ['t','3']]] ∧
    batchIds theGatherZeroRequest = [[['t','1']], [['t','2']], [['t','3']]] ∧
    batchIds theGatherBigRequest = [[['t','1']], [['t','2']], [['t','3']]] ∧
    batchIds theGatherWallRequest = [[['t','2']], [['t','1'], ['t','3']]] ∧
    batchIds theGatherOptionalRequest = [[['t','1'], ['t','3']], [['t','2']]] ∧
    batchIds theGatherWindowRequest = [[['t','1']], [['t','2']], [['t','3']]] := by decide

/-! ### §8.2 step 5's cursor, run rather than argued (P5b, the second half)

Four candidates, none of them gatherable (`remaining` 50 against `batch_max_min` 20), so each
leads a group of its own and the batching below is a no-op: what these measure is the **filter
at a slot** and nothing else.  The §4.3 Wednesday at 14:00 cuts four slots at energies
3, 3, 2, 2 and the day's remaining budget is four, so the budget never binds and every `none`
below is a filter's doing. -/

/-- One cursor candidate: `remaining` past `batch_max_min`, so it never shares a block. -/
def cCand (id : List Char) (ci : Fin 6) (pm : Nat) (l : Field.Loc) (sp : Bool)
    (h : Look.PlanFacts.wf { planFacts pm l with splittable := sp } = true) :
    Look.Cand × Option Look.Floor :=
  (⟨id, ci, some 0, 50, none, false, false, false, false, false, false, none,
     ⟨{ planFacts pm l with splittable := sp }, h⟩⟩, none)

/-- `^c1` fits anywhere; `^c2` is an errand (`loc:out`) and the day is being lived in the
lounge; `^c3` is `ci 5` and no slot of this day is that good; `^c4` is `ci 2`, asks for four
hours and is splittable. -/
def witCursorCands : List (Look.Cand × Option Look.Floor) :=
  [cCand ['c','1'] 3 60  .any  true (by decide),
   cCand ['c','2'] 3 60  .out  true (by decide),
   cCand ['c','3'] 5 60  .any  true (by decide),
   cCand ['c','4'] 2 240 .any  true (by decide)]

def theCursorRequest : PlanReq := { theRequest with cands := ⟨witCursorCands, by decide⟩ }

/-- The same four with `^c2`'s `loc:` changed from `out` to `lounge`, and nothing else. -/
def witCursorLocCands : List (Look.Cand × Option Look.Floor) :=
  [cCand ['c','1'] 3 60  .any    true (by decide),
   cCand ['c','2'] 3 60  .lounge true (by decide),
   cCand ['c','3'] 5 60  .any    true (by decide),
   cCand ['c','4'] 2 240 .any    true (by decide)]

def theCursorLocRequest : PlanReq := { theRequest with cands := ⟨witCursorLocCands, by decide⟩ }

/-- The same four with `^c3`'s `ci` changed from 5 to 3, and nothing else. -/
def witCursorCiCands : List (Look.Cand × Option Look.Floor) :=
  [cCand ['c','1'] 3 60  .any true (by decide),
   cCand ['c','2'] 3 60  .out true (by decide),
   cCand ['c','3'] 3 60  .any true (by decide),
   cCand ['c','4'] 2 240 .any true (by decide)]

def theCursorCiRequest : PlanReq := { theRequest with cands := ⟨witCursorCiCands, by decide⟩ }

/-- The same four with `^c4` made `atomic`, and nothing else. -/
def witCursorAtomicCands : List (Look.Cand × Option Look.Floor) :=
  [cCand ['c','1'] 3 60  .any true  (by decide),
   cCand ['c','2'] 3 60  .out true  (by decide),
   cCand ['c','3'] 5 60  .any true  (by decide),
   cCand ['c','4'] 2 240 .any false (by decide)]

def theCursorAtomicRequest : PlanReq :=
  { theRequest with cands := ⟨witCursorAtomicCands, by decide⟩ }

/-- The same, `atomic`, asking for **three** hours rather than four — the run the day can
actually give it. -/
def witCursorAtomicFitCands : List (Look.Cand × Option Look.Floor) :=
  [cCand ['c','1'] 3 60  .any true  (by decide),
   cCand ['c','2'] 3 60  .out true  (by decide),
   cCand ['c','3'] 5 60  .any true  (by decide),
   cCand ['c','4'] 2 180 .any false (by decide)]

def theCursorAtomicFitRequest : PlanReq :=
  { theRequest with cands := ⟨witCursorAtomicFitCands, by decide⟩ }

/-- Which group took each slot, by its members' ids — `none` for a slot the filter left empty. -/
def assignIds (r : PlanReq) : List (Option (List Id)) :=
  r.assignFold.slotOf.map (fun o => o.bind (fun gi =>
    (r.assignFold.groups[gi]?).map (fun g => g.members.map (fun x => x.cand.id))))

/-- The same walk at a budget the caller names — fork `remaining_budget`, which is a *local* of
`plan()` and not a field of the day. -/
def assignAt (r : PlanReq) (budget : Nat) : Assign :=
  r.energisedSlots.zipIdx.foldl (r.assignStep r.todaySlots r.todayBreaks budget) r.assignStart

def assignIdsAt (r : PlanReq) (budget : Nat) : List (Option (List Id)) :=
  (assignAt r budget).slotOf.map (fun o => o.bind (fun gi =>
    ((assignAt r budget).groups[gi]?).map (fun g => g.members.map (fun x => x.cand.id))))

set_option maxRecDepth 100000 in
/-- **The four candidates lead four groups of their own**, so nothing below is about §7.5: the
batching is a no-op here and the cursor is the only thing under test. -/
theorem the_cursor_request_batches_nothing :
    rankedIds theCursorRequest = [['c','1'], ['c','2'], ['c','3'], ['c','4']] ∧
    groupIds theCursorRequest =
      [[['c','1']], [['c','2']], [['c','3']], [['c','4']]] := by decide

set_option maxRecDepth 100000 in
/-- **The day's four slots, their energies and the budget** — the ground every witness below
stands on, computed rather than assumed. -/
theorem the_cursor_requests_day_is_four_slots :
    theCursorRequest.energisedSlots.map (fun p => p.1.val) = [3, 3, 2, 2] ∧
    remainingBudget theCursorRequest = 4 ∧
    theCursorRequest.curLoc = Field.Loc.lounge := by decide

set_option maxRecDepth 100000 in
/-- **The cursor, computed.**  `^c1` takes the first slot because it is first in §7.4's order
and fits it.  At the second slot `^c1` is done (its whole commitment went into one 60-minute
block), `^c2` is refused for its `loc:`, `^c3` for its `ci`, and `^c4` takes it and the two
after it — four hours asked for, three given, which is the group still owing minutes at the end
of the day. -/
theorem the_cursor_fills_the_day_in_key_order :
    assignIds theCursorRequest =
      [some [['c','1']], some [['c','4']], some [['c','4']], some [['c','4']]] ∧
    theCursorRequest.assignFold.used = 4 := by decide

set_option maxRecDepth 100000 in
/-- **`loc_ok` is the only reason `^c2` was passed over.**  The same four with `^c2`'s `loc:`
changed from `out` to `lounge` — one field, nothing else — and `^c2` takes the second slot,
pushing `^c4` back by one.  Without this line the theorem above would be satisfied by a cursor
that never looked at `loc:` at all and simply preferred `^c4`. -/
theorem the_cursor_refuses_a_slot_in_the_wrong_place :
    assignIds theCursorLocRequest =
      [some [['c','1']], some [['c','2']], some [['c','4']], some [['c','4']]] := by decide

set_option maxRecDepth 100000 in
/-- **And the energy filter is the only reason `^c3` was.**  `^c3`'s `ci` changed from 5 to 3 —
one field — and it takes the second slot, whose energy is 3.  It still never reaches slots three
and four, whose energy is 2: `ci ≤ energy` is a comparison and not a flag. -/
theorem the_cursor_refuses_a_slot_that_is_not_good_enough :
    assignIds theCursorCiRequest =
      [some [['c','1']], some [['c','3']], some [['c','4']], some [['c','4']]] := by decide

set_option maxRecDepth 100000 in
/-- **An `atomic` group takes a slot only when the whole run is there.**  `^c4` asks for four
hours and the day has three free after the first slot, so the same candidate that is placed
three times when splittable is placed **not at all** when `atomic` — and the day loses the
afternoon rather than starting a job it cannot finish. -/
theorem an_atomic_group_needs_its_whole_run :
    assignIds theCursorAtomicRequest = [some [['c','1']], none, none, none] := by decide

set_option maxRecDepth 100000 in
/-- **And the test is the run's length, not the `atomic` flag.**  The same `atomic` candidate
asking for the three hours the day can actually give takes all three slots.  Without this line
the theorem above would be satisfied by a cursor that refused every `atomic` group. -/
theorem an_atomic_group_that_fits_is_placed :
    assignIds theCursorAtomicFitRequest =
      [some [['c','1']], some [['c','4']], some [['c','4']], some [['c','4']]] := by decide

set_option maxRecDepth 100000 in
/-- **A planned break does not break the run, and a gap that is not one does.**  The three-hour
run above crosses step 3's own 20-minute break (`todayBreaks`' second entry is exactly the gap
between the second and third slots).  Given the same slots and the same need with **no** breaks
declared, the identical walk answers `false` — which is fork `contiguous_fits`' "sitting through
the break the planner itself inserted is not a context switch", measured. -/
theorem a_planned_break_does_not_break_an_atomic_run :
    contiguousFits theCursorRequest.todaySlots [none, none, none, none]
      theCursorRequest.todayBreaks 1 180 = true ∧
    contiguousFits theCursorRequest.todaySlots [none, none, none, none] [] 1 180 = false := by
  decide

set_option maxRecDepth 100000 in
/-- **An assigned slot inside the run breaks it too** — the fork's first clause.  The same walk
with the third slot already taken cannot find three hours from the second. -/
theorem an_assigned_slot_breaks_an_atomic_run :
    contiguousFits theCursorRequest.todaySlots [none, none, some 0, none]
      theCursorRequest.todayBreaks 1 180 = false := by decide

set_option maxRecDepth 100000 in
/-- **The budget stops the walk**, and it stops it at the slot rather than at the day: the same
four candidates at a remaining budget of two fill two slots and leave the rest of the afternoon
to Rest.  This is the clause `remaining_budget` owns, and it is the one §9's "→ drops: …" reads
when a block runs long. -/
theorem the_budget_stops_the_cursor :
    assignIdsAt theCursorRequest 2 = [some [['c','1']], some [['c','4']], none, none] ∧
    assignIdsAt theCursorRequest 0 = [none, none, none, none] ∧
    assignIdsAt theCursorRequest 4 = assignIds theCursorRequest := by decide

/-- Which groups pass §8.2 step 5's filter at slot `i` of an empty day. -/
def fitsAt (r : PlanReq) (i : Nat) : List Bool :=
  match r.energisedSlots[i]? with
  | Option.none => []
  | some (e, s) => r.assignStart.groups.map (fun g =>
      r.groupFitsSlot r.todaySlots r.assignStart.slotOf r.todayBreaks i e s g)

set_option maxRecDepth 100000 in
/-- **Two groups pass the filter at the first slot, and §7.4's order is the only thing that
chooses between them.**  `^c1` and `^c4` both fit it — `^c4`'s `ci 2` is inside the slot's
energy 3 and it has no `loc:` — so `the_cursor_fills_the_day_in_key_order`'s first entry is the
cursor taking the **first** group that fits and not the best-fitting one.  A `pick` that
answered the last fitting group would satisfy every other witness in this section and fail that
one; this line is what says so. -/
theorem two_groups_fit_the_first_slot_and_the_order_decides :
    fitsAt theCursorRequest 0 = [true, false, false, true] := by decide

/-! ############################################################################
## 16. The ceiling: two of the eleven are FALSE on a day the planner produces
     — stage 6, run W-19, track G
############################################################################

Section 14 answered *how much of the battery a witness can make bite*: **seven of the eleven**
have a subject at `theCensusRequest`.  `PlanCheck.dayPlan_ok_from_now_except_the_two_comparisons`
answers *how much of §6.1's lift is proved*: **nine of the eleven**, at every eligibility, over
`PlanCheck.withoutPast`'s day.  Neither answers the question a reader of those two numbers asks
next, which is whether the remaining two conjuncts are **unproved** or **false**.

They are false, and this section proves it.  The claim itself is not new — `PlanCheck.lean`
has said *"the `∀ el` form is **false** of P1's body"* since W-14, and design §6.3 rows 4 and 5
predict it from the fork's proptest header.  What was missing is the thing this campaign keeps
finding missing: **nothing computed it.**  A sentence saying a statement is false, in a
repository whose whole method is that a claim is a theorem, is a claim of having checked that
was never made (AGENTS §5.2, §9.2).

**One request settles four statements**, and it is one line of the morning's log away from the
census request:

| statement | verdict here |
|---|---|
| `Goals.plan_is_monotone_in_rank`, as stage 6 wrote it | **refuted** |
| `Goals.plan_puts_hot_before_the_queue`, as stage 6 wrote it | **refuted** |
| `∀ el r, PlanCheck.planOk el r (Planner.dayPlan r) = true` | **refuted** |
| `∀ el r, PlanCheck.planOk el r (PlanCheck.withoutPast r (Planner.dayPlan r)) = true` | **refuted** |

and the nine that *are* proved keep holding at the very same request, so **exactly two** fail
and the nine-of-eleven is a **ceiling** rather than a stopping place.

**Why the witness is one line of log and not a new plan.**  `censusWitness`' store already
holds what the two comparisons need: `m1` and `m2`, one document, ranks 1 and 2, both `ci:5`,
equal `rootPrio`, and `hot` on `m1` alone (`the_census_witness_holds_the_wall_and_two_ranked
_siblings`).  At `theCensusRequest` both are assigned — the log worked both, and `m1` is the
one running — so both checks pass.  Take `m1`'s two log lines away and run **`m2`** instead,
and the hot sibling that ranks first is the one the day never mentions.  Nothing else moves:
same plan, same lookahead input, same configuration, same builder.

**What it does NOT show, said before the theorems rather than after.**  This is not a defect in
the planner.  `m1` is missing from the day because **the assign fold is not written** — §8.2
step 5 is P5's and `Planner.dayRows` places steps 1, 2 and choice 5b's reservation only.  Nor
does it show that Planner.eligibleAt cannot rescue the two: an eligibility predicate that
answers `false` for `m1` at every row of this day makes both conjuncts hold again, and whether
the real one does is P5's decision.  **That is the inheritance this section is for** — it names
the decision instead of leaving it inside a count.  See README gap 850. -/

/-- The morning's log with `m1`'s block taken out: `witLines`' wake and arrive, then its
`start`/`done` pair for `m2`.  The four lines are `witLines`' own bytes, taken rather than
respelled (`List.take`/`List.drop`, numbers 1, 2, 5, 6). -/
def queuedLines : List Log.Line := witLines.take 2 ++ witLines.drop 4

set_option maxRecDepth 40000 in
theorem queuedRun_resumes_ok : runOk Cal.chicago 739867 queuedLines = true := by decide

def queuedRun : Seal.Run :=
  match h : Seal.resumeRun Cal.chicago 739867 (Seal.Ckpt.empty Cal.chicago) queuedLines with
  | .ok run => run
  | .error _ => absurd queuedRun_resumes_ok (by simp [runOk, h])

theorem queuedRun_resumes :
    Seal.resumeRun Cal.chicago 739867 (Seal.Ckpt.empty Cal.chicago) queuedLines
      = .ok queuedRun := by
  unfold queuedRun
  split
  · rename_i run h; rw [h]
  · rename_i e h; exact absurd queuedRun_resumes_ok (by simp [runOk, h])

/-- §9's `state.active`, with **`m2`** running — `theRunningBlock` with one character changed,
so that the item choice 5b reserves is the sibling that ranks *second*. -/
def theQueuedBlock : ActiveBlock :=
  ⟨['m','2'], ⟨(Cal.instantOf Cal.chicago 739867 820).sec, 0⟩, 90, false⟩

def theQueuedState : RuntimeIn := { RuntimeIn.empty with active := some theQueuedBlock }

def witReqInQueued : PlanReqIn :=
  { witReqIn with docs := censusWitness, lines := queuedLines, state := theQueuedState }

/-- **The queued request**: the §4.3 Wednesday at 14:00 with the census store, a log that
worked only `m2`, and `m2` running.  `m1` — hot, ranked first, `ci:5`, in the store — reaches
no row of the day at all. -/
def theQueuedRequest : PlanReq :=
  ⟨censusPlan, queuedRun, witInput, theQueuedState, Capped.nil, witPrio, Capped.nil, none⟩

/-- **The builder accepts it** — by rewriting with the four stage equations, never by a
`decide` that holds the load, the resume and the lookahead at once. -/
theorem witBuildsQueued : mkPlanReq? witReqInQueued = .ok theQueuedRequest := by
  obtain ⟨ht, hz, hd, hw, -⟩ := witInput_fields
  unfold mkPlanReq? witReqInQueued witReqIn theQueuedRequest
  simp only [censusPlan_loads, witInput_decodes]
  rw [if_neg (by
    rw [hw, hz, hd]
    simp only [Look.DayCfg.shipped, Look.CutCfg.shipped, ne_eq]
    exact not_not_intro the_census_witness_indexes_the_calendars_one_wall.symm)]
  rw [hz, ht, queuedRun_resumes]
  simp only [Capped.ofList?_nil, mkRoutines?_of_none]

/-- `hagree`, from the builder and not from a `decide`. -/
theorem theQueuedRequest_wallsAgree : theQueuedRequest.wallsAgree = true :=
  mkPlanReq?_ok_wallsAgree witReqInQueued theQueuedRequest witBuildsQueued

/-- `hactive` and `hday`, the two R10 hypotheses both lifts carry. -/
theorem the_queued_request_agrees :
    theQueuedRequest.activeAgrees = true ∧ theQueuedRequest.dayAgrees = true := by decide

/-- `hnowcal`: the instant being planned is inside the calendar. -/
theorem the_queued_request_is_inside_the_calendar :
    theQueuedRequest.now.sec + 1 < LogStamp.yearEnd := by decide

set_option maxRecDepth 40000 in
/-- `hplain`, **reused and not re-proved**: this request's plan is `censusPlan` and its
lookahead input is `witInput`, exactly as the census request's are, so the statement is the
same one (AGENTS §5.3 — a second proof of one fact is a second copy of it). -/
theorem the_queued_request_is_plain :
    ∀ (i : Id) (e : Entity) (a b : Field.DT),
      theQueuedRequest.plan.val.store.get i = some e →
      e.val.shape = Field.Shape.interval a b →
      e.val.buffer = none ∧
        theQueuedRequest.dayStart ≤ (Cal.instantOf theQueuedRequest.tz a.day a.time).sec ∧
        (Cal.instantOf theQueuedRequest.tz b.day b.time).sec ≤ theQueuedRequest.dayEnd ∧
        (Cal.instantOf theQueuedRequest.tz a.day a.time).sec
          < (Cal.instantOf theQueuedRequest.tz b.day b.time).sec ∧
        (Cal.instantOf theQueuedRequest.tz b.day b.time).sec < LogStamp.yearEnd :=
  the_census_request_is_plain

set_option maxRecDepth 40000 in
/-- **The day, end to end**: `m2`'s replayed block, the written wall, §8.2 choice 5b's
reservation of `m2`, and §16's two evening rows.  Five rows, and **`m1` is in none of them**. -/
theorem the_queued_day_is_the_second_sibling_twice :
    (dayPlan theQueuedRequest).segments.map
        (fun s => (s.val.start, s.val.stop, s.val.kind, s.val.item))
      = [((Cal.instantOf Cal.chicago 739867 545).sec, (Cal.instantOf Cal.chicago 739867 605).sec,
          SegKind.block, some (['m','2'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 770).sec, (Cal.instantOf Cal.chicago 739867 830).sec,
          SegKind.wall, some (['g','1'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 840).sec, (Cal.instantOf Cal.chicago 739867 880).sec,
          SegKind.block, some (['m','2'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 1290).sec,
          (Cal.instantOf Cal.chicago 739867 1320).sec, SegKind.windDown, none),
         ((Cal.instantOf Cal.chicago 739867 1320).sec, (Cal.instantOf Cal.chicago 739868 0).sec,
          SegKind.sleep, none)] := by
  decide

set_option maxRecDepth 40000 in
/-- **The four populations the two refutations turn on**, computed: the day assigns `m2` and
only `m2`, on the whole day and on the restricted one both; some row carries `m2`; **no** row
carries `m1`.  The last two are the halves `hotBeforeQueue` reads, and they are stated as
`List.any`/`List.all` rather than as an existential so that one `decide` settles them. -/
theorem the_queued_day_assigns_the_second_sibling_only :
    assignedOf (dayPlan theQueuedRequest) = [['m','2'], ['m','2']] ∧
      assignedOf (PlanCheck.withoutPast theQueuedRequest (dayPlan theQueuedRequest))
        = [['m','2']] ∧
      ((dayPlan theQueuedRequest).segments.any
        (fun s => s.val.item == some (['m','2'] : Id))) = true ∧
      ((dayPlan theQueuedRequest).segments.all
        (fun s => s.val.item != some (['m','1'] : Id))) = true := by
  decide

set_option maxRecDepth 40000 in
/-- **The two comparisons answer `false`, and so does the whole battery** — on the day
`Planner.dayPlan` really produced, with **no mutation at all**, at the permissive eligibility,
on the whole day and on `PlanCheck.withoutPast`'s day alike.

This is the second no-mutation bite in this module (`the_mid_break_day_lays_a_block_across_a
_break` is the first), and it is the stronger kind: the battery is refusing a day for a
*comparison* between two candidates rather than for an interval overlap. -/
theorem the_two_comparisons_are_false_at_the_queued_request :
    PlanCheck.monotoneInRank permissive theQueuedRequest (dayPlan theQueuedRequest) = false ∧
      PlanCheck.hotBeforeQueue permissive theQueuedRequest (dayPlan theQueuedRequest) = false ∧
      PlanCheck.planOk permissive theQueuedRequest (dayPlan theQueuedRequest) = false ∧
      PlanCheck.monotoneInRank permissive theQueuedRequest
        (PlanCheck.withoutPast theQueuedRequest (dayPlan theQueuedRequest)) = false ∧
      PlanCheck.hotBeforeQueue permissive theQueuedRequest
        (PlanCheck.withoutPast theQueuedRequest (dayPlan theQueuedRequest)) = false ∧
      PlanCheck.planOk permissive theQueuedRequest
        (PlanCheck.withoutPast theQueuedRequest (dayPlan theQueuedRequest)) = false := by
  decide

set_option maxRecDepth 40000 in
/-- **And the other nine still hold at that same request** — which is what makes the failure
*exactly two* rather than "the battery fails here".  `planOkCore` is the seven, computed on
both days; `impossibleKept` and `batchDoesNotReachPast` are the two that hold because their
subject is empty at every request (`PlanCheck.impossibleKept_is_true_because_its_subject_is
_empty` and its sibling).

Without this conjunction the refutation above would be compatible with three of the eleven
failing, or seven — and README gap 684 is the record of what counting that by hand costs. -/
theorem the_other_nine_hold_where_the_two_fail :
    PlanCheck.planOkCore theQueuedRequest (dayPlan theQueuedRequest) = true ∧
      PlanCheck.planOkCore theQueuedRequest
        (PlanCheck.withoutPast theQueuedRequest (dayPlan theQueuedRequest)) = true ∧
      PlanCheck.impossibleKept permissive theQueuedRequest
        (PlanCheck.withoutPast theQueuedRequest (dayPlan theQueuedRequest)) = true ∧
      PlanCheck.batchDoesNotReachPast permissive theQueuedRequest
        (PlanCheck.withoutPast theQueuedRequest (dayPlan theQueuedRequest)) = true := by
  decide

/-- **The nine-of-eleven lift, fired at this request** — not a `decide`, but
`PlanCheck.dayPlan_ok_from_now_except_the_two_comparisons` with every hypothesis discharged by
a theorem above.  Two theorems stating the same `true` is not a duplication here and the
difference is the point: `the_other_nine_hold_where_the_two_fail` *computes* the nine at one
request, and this *derives* them from the general lift.  A day on which the computation and
the lift disagreed would be a defect in the lift. -/
theorem the_lift_applies_at_the_queued_request :
    PlanCheck.planOkCore theQueuedRequest
      (PlanCheck.withoutPast theQueuedRequest (dayPlan theQueuedRequest)) = true ∧
      PlanCheck.impossibleKept permissive theQueuedRequest
        (PlanCheck.withoutPast theQueuedRequest (dayPlan theQueuedRequest)) = true ∧
      PlanCheck.batchDoesNotReachPast permissive theQueuedRequest
        (PlanCheck.withoutPast theQueuedRequest (dayPlan theQueuedRequest)) = true :=
  PlanCheck.dayPlan_ok_from_now_except_the_two_comparisons permissive theQueuedRequest
    theQueuedRequest_wallsAgree the_queued_request_agrees.1 the_queued_request_agrees.2
    the_queued_request_is_inside_the_calendar the_queued_request_is_plain

/-! ### §6.1's lift at an arbitrary eligibility is REFUTED, both ways round

Design §6.1 writes the lift `planOk r (dayPlan r) = true`, with no eligibility parameter,
because it was written before §6.3 found that four of the eleven need one.  The two honest
readings of it once the parameter exists are the `∀ el` form and the `∃ el` form, and §6.3
disposes of the second: `fun _ _ _ _ => false` satisfies it.  The first is below, refuted at
both of the days the stage's two lifts are stated over.

`PlanCheck.lean` has asserted the whole-day half in prose since W-14 and the restricted-day
half has never been stated at all. -/

/-- **The `∀ el` form of §6.1's lift, over the whole day, is false.** -/
theorem dayPlan_ok_at_every_eligibility_is_refuted :
    ¬ (∀ (el : PlanCheck.Eligible) (r : PlanReq), PlanCheck.planOk el r (dayPlan r) = true) := by
  intro h
  exact absurd (h permissive theQueuedRequest)
    (by rw [the_two_comparisons_are_false_at_the_queued_request.2.2.1]; simp)

/-- **And over `PlanCheck.withoutPast`'s day too** — the day
`PlanCheck.dayPlan_ok_from_now_except_the_two_comparisons` is stated over, so this is the one
that says the nine are a ceiling.  It is a separate statement and not a corollary: restricting
the day removes rows, which can only make a `∀`-shaped checker *easier* to satisfy, so the
whole-day refutation does not imply this one.  (At `theCensusRequest` the difference is
visible in the other direction: `noBlockOverABreak` has a subject on both days, and the Block
rows `withoutPast` removes are exactly the ones `plan_places_no_block_over_a_break` could not
be proved about.) -/
theorem dayPlan_ok_from_now_at_every_eligibility_is_refuted :
    ¬ (∀ (el : PlanCheck.Eligible) (r : PlanReq),
        PlanCheck.planOk el r (PlanCheck.withoutPast r (dayPlan r)) = true) := by
  intro h
  exact absurd (h permissive theQueuedRequest)
    (by rw [the_two_comparisons_are_false_at_the_queued_request.2.2.2.2.2]; simp)

/-! ### The two `Goals.lean` statements, refuted

Design §6.3 rows 4 and 5 record both as false against the fork and hand the **restatements** to
P5, which is why neither goal leaves `Goals.lean` here: a restatement without its refutation is
a weakening (AGENTS §3.1 item 3), and the restatement needs Planner.eligibleAt, which does not
exist (README gap 365).  This is `Goals.plan_tail_drop`'s situation exactly — refuted in this
module at W-15, still standing in `Goals.lean`, with the refutation named at its doc comment —
and it is handled the same way.  Burn-down **9, unchanged**, and README gap 851 says why. -/

set_option maxRecDepth 40000 in
/-- **`Goals.plan_is_monotone_in_rank` as stage 6 wrote it is FALSE** (AGENTS §3.1 item 3, D5).

`m1` and `m2` are one document's two siblings at equal `rootPrio` and equal `effectiveCi`,
ranked 1 and 2.  The day assigns `m2` and does not assign `m1`, so the goal's conclusion fails
under every one of its hypotheses.  Design §6.3 predicted this from the fork's proptest header
— *"step 5 skips a `loc:`-constrained, `atomic` or `max:`-capped item for reasons the invariant
is not about"* — and the reason **here** is simpler and is not in that list: there is no step 5
yet, so nothing can assign `m1` at all.

The restatement is **P5**'s and takes the two candidates to be additionally comparable
(`PlanCheck.eligibleSomewhere` at Planner.eligibleAt). -/
theorem plan_is_monotone_in_rank_as_stage_6_wrote_it_is_refuted :
    ¬ (∀ (r : PlanReq) (i j : Id) (e f : Entity),
        r.plan.val.store.get i = some e → r.plan.val.store.get j = some f →
        rootPrio r.plan.val i = rootPrio r.plan.val j →
        effectiveCi r.plan.val i = effectiveCi r.plan.val j →
        e.val.live.doc = f.val.live.doc →
        e.val.live.rank < f.val.live.rank →
        j ∈ assignedOf (dayPlan r) →
        i ∈ assignedOf (dayPlan r)) := by
  intro h
  obtain ⟨hass, -, -, -⟩ := the_queued_day_assigns_the_second_sibling_only
  cases hm1 : censusPlan.val.store.get ['m','1'] with
  | none => exact absurd hm1 (by decide)
  | some e =>
    cases hm2 : censusPlan.val.store.get ['m','2'] with
    | none => exact absurd hm2 (by decide)
    | some f =>
      have h1 : (censusPlan.val.store.get ['m','1']).map
          (fun x => (x.val.live.doc, x.val.live.rank)) = some (1, 1) := by decide
      rw [hm1, Option.map_some] at h1
      have h2 : (censusPlan.val.store.get ['m','2']).map
          (fun x => (x.val.live.doc, x.val.live.rank)) = some (1, 2) := by decide
      rw [hm2, Option.map_some] at h2
      injection Option.some.inj h1 with hed her
      injection Option.some.inj h2 with hfd hfr
      have hd : e.val.live.doc = f.val.live.doc := by rw [hed, hfd]
      have hr : e.val.live.rank < f.val.live.rank := by rw [her, hfr]; decide
      have hp : rootPrio censusPlan.val ['m','1'] = rootPrio censusPlan.val ['m','2'] :=
        the_census_witness_holds_the_wall_and_two_ranked_siblings.2.2.2.2.1
      have hc : effectiveCi censusPlan.val ['m','1'] = effectiveCi censusPlan.val ['m','2'] := by
        decide
      have hin : (['m','2'] : Id) ∈ assignedOf (dayPlan theQueuedRequest) := by
        rw [hass]; simp
      have := h theQueuedRequest ['m','1'] ['m','2'] e f hm1 hm2 hp hc hd hr hin
      rw [hass] at this
      simp at this

set_option maxRecDepth 40000 in
/-- **`Goals.plan_puts_hot_before_the_queue` as stage 6 wrote it is FALSE** (AGENTS §3.1 item
3, D5).

`m1` carries §7.2's `hot` flag and `m2` does not; the day holds two rows carrying `m2` and
**none** carrying `m1`, so there is no row to be "before the queue" at.  Design §6.3 row 5
predicted it — *"a dep-blocked or `Waiting` hot item is not assigned at all"* — and, as with
the rank law, the reason here is that step 5 is unwritten rather than that `m1` is blocked.

The restatement is **P5**'s and adds that the hot item is eligible at some slot of the day. -/
theorem plan_puts_hot_before_the_queue_as_stage_6_wrote_it_is_refuted :
    ¬ (∀ (r : PlanReq) (i j : Id) (e f : Entity) (sj : WfSeg),
        r.plan.val.store.get i = some e → r.plan.val.store.get j = some f →
        Field.Flag.hot ∈ e.val.flags → Field.Flag.hot ∉ f.val.flags →
        sj ∈ (dayPlan r).segments → sj.val.item = some j →
        ∃ si ∈ (dayPlan r).segments, si.val.item = some i ∧
          si.val.start ≤ sj.val.start) := by
  intro h
  obtain ⟨-, -, hany, hall⟩ := the_queued_day_assigns_the_second_sibling_only
  cases hm1 : censusPlan.val.store.get ['m','1'] with
  | none => exact absurd hm1 (by decide)
  | some e =>
    cases hm2 : censusPlan.val.store.get ['m','2'] with
    | none => exact absurd hm2 (by decide)
    | some f =>
      have h1 : (censusPlan.val.store.get ['m','1']).map (fun x => x.val.flags)
          = some [Field.Flag.hot] := by decide
      rw [hm1, Option.map_some] at h1
      have h2 : (censusPlan.val.store.get ['m','2']).map (fun x => x.val.flags)
          = some [] := by decide
      rw [hm2, Option.map_some] at h2
      have hhot : Field.Flag.hot ∈ e.val.flags := by rw [Option.some.inj h1]; simp
      have hnot : Field.Flag.hot ∉ f.val.flags := by rw [Option.some.inj h2]; simp
      obtain ⟨sj, hsj, hji⟩ := List.any_eq_true.1 hany
      obtain ⟨si, hsi, hii, -⟩ :=
        h theQueuedRequest ['m','1'] ['m','2'] e f sj hm1 hm2 hhot hnot hsj (by simpa using hji)
      have := List.all_eq_true.1 hall si hsi
      simp [hii] at this


/-! ### The two comparisons' subjects, counted — and one number in this file was wrong

`the_battery_census_at_the_census_request` counts a checker's subject by filtering the day's
**segments**.  Two of the eleven do not range over segments at all: `PlanCheck.monotoneInRank`
and `PlanCheck.hotBeforeQueue` range over **pairs of store ids**, and the census's `= true`
rows for them are the only two it takes on trust.  `PlanCheck.rankSubjects` and
`PlanCheck.hotSubjects` close that, in the census's own idiom — a `filterMap` over the thing
the checker quantifies over, whose length is the count.  They are **populations, not
checkers**: each spells the antecedents of `PlanCheck.rankPairOk` / `PlanCheck.hotPairOk` and
neither spells the conclusion, so a bug in one cannot make a checker pass.

**They were declared here until W-21 and are declared beside their checkers now** (AGENTS
§5.3's *"the fix was deletion, not a bridge"*): `PlanCheck.subjectOf` is the census as a
function and needs both, and a second Bool-valued copy of either in `PlanCheck.lean` would
have been the class this kernel is named after.  Nothing else moved and nothing was
re-implemented. -/

set_option maxRecDepth 40000 in
/-- **The refutation above is not vacuous**: both comparisons really do range over something
at `theQueuedRequest`, on the whole day and on `PlanCheck.withoutPast`'s day alike, so their
`false` is earned rather than an empty quantifier answering the wrong way (AGENTS §5.2).  The
rank pair is `(m1, m2)`; the hot pairs are `(m1, m2)` and `(m1, g1)` — the calendar's meeting
has a row and carries no `hot`, so it is a queued item this rule is about too. -/
theorem the_two_comparisons_have_subjects_where_they_bite :
    PlanCheck.rankSubjects permissive theQueuedRequest (dayPlan theQueuedRequest)
        = [(['m','1'], ['m','2'])] ∧
      PlanCheck.hotSubjects permissive theQueuedRequest (dayPlan theQueuedRequest)
        = [(['m','1'], ['m','2']), (['m','1'], ['g','1'])] ∧
      PlanCheck.rankSubjects permissive theQueuedRequest
          (PlanCheck.withoutPast theQueuedRequest (dayPlan theQueuedRequest))
        = [(['m','1'], ['m','2'])] ∧
      (PlanCheck.hotSubjects permissive theQueuedRequest
          (PlanCheck.withoutPast theQueuedRequest (dayPlan theQueuedRequest))).length = 2 := by
  decide

set_option maxRecDepth 40000 in
/-- **And the correction this file owed.**  Section 11's `storedWitness` doc comment said
`Boundary.lookWallPlan`'s one-id store *"leaves five of the eleven checkers with nothing to
range over"*.  It is **not five**, under any reading, and nothing in the repository computed
it.  Measured here: at `theRunningRequest` the two comparisons have **no** subject at all —
one id cannot make a pair — so with `the_battery_census_at_the_reserved_day`'s **four of
seven** over `checksCore`, and `impossibleKept` and `batchDoesNotReachPast` empty at every
request (`PlanCheck.impossibleKept_is_true_because_its_subject_is_empty` and its sibling), the
count is **four of eleven with a subject and seven without**.

Of those seven, **three** are starved by the witness — `noBlockOverABreak` wants a log with a
break, and the two comparisons want a second id — and **four** by the planner, which is gap
650's four.  The sentence conflated the two halves and used a number matching neither; it is
corrected in place and says what it read.  README gap 852. -/
theorem the_one_id_store_gives_neither_comparison_a_subject :
    theRunningRequest.plan.val.store.dom = [['g','1']] ∧
      PlanCheck.rankSubjects permissive theRunningRequest (dayPlan theRunningRequest) = [] ∧
      PlanCheck.hotSubjects permissive theRunningRequest (dayPlan theRunningRequest) = [] := by
  decide

/-! ############################################################################
## 17. §8.2 step 6, run rather than argued (stage 6 step P6, AGENTS §5.2)

**The first request in this repository that carries a window instance.**  Every `PlanReq` above
has `routines := []` (`the_witness_carries_no_routine`), so until now §8.2 step 2's placement
fold and every law about it ranged over an empty list, and step 6 had nothing at all.  This
section builds the day W-15's P2 and this step's P6 are about and computes what each does to it.

**The day.**  §4.3's Wednesday at 14:00, the same calendar wall, plus a `routines.md` of three
lines.  Two instances are sent: `warmup`, **mandatory**, 16:00–17:00 for 60 minutes, which step
2 places at the earliest feasible position — 16:00; and `stretch`, not mandatory and with no
`pref:` anchor, 14:00–19:00 for 30 minutes, which step 2 therefore **defers** (`deferred :=
true`, no position).  That leaves the afternoon in two free stretches, 14:00–16:00 and
17:00–19:00, and their starts are at **different energies** — 4 and 2 — which is what makes the
rule under test the only thing that decides.

**What the four theorems isolate.**
* the earliest rule and the lowest-energy rule **disagree at these very arguments**:
  `Planner.earliestFree` answers 14:00 and `Planner.PlanReq.lowestFree` answers 17:00, so the
  end-to-end placement at 17:00–17:30 is step 6's rule and not step 2's leaking through;
* a **tie** on energy goes to the earlier position, computed at two stretches whose starts are
  both at energy 3;
* **one field differs** — the instance's `durMin`, 30 minutes against 150 — and the day that had
  room has none, so the instance ends in `Planner.Note.noPosition` instead of on the timeline;
* an instance whose window has **closed** (a `win:11:30-13:30` line carried into the afternoon,
  whose span comes back inverted) is passed over and is **not** reported — §5.3's expiry is not
  a placement failure, and the note list stays empty.

**The displacement is witnessed at its own arguments and not through a request, and README gap
903 says why**: no `PlanReq` reaches `Planner.PlanReq.displaceInto`, because step 2 places a
mandatory instance wherever a stretch as wide as it is free, and a slot wide enough inside its
window is exactly such a stretch.  The three victim theorems and the re-placement theorem
therefore feed the functions directly — which is what gives them a subject at all (README gap
875's lesson). -/

/-- §4.3's Wednesday calendar, and a `routines.md` of three lines: one mandatory anchor, one
that will be deferred, and one whose daily hours closed this morning. -/
def routineWitness : List ReqDoc :=
  [⟨"calendar/2026-W37.md", none,
     ["- [ ] 3 Meeting w/ host      at:2026-09-09T12:50/13:50 loc:zoom ^g1".toList]⟩,
   ⟨"routines.md", none,
     ["- warmup win:16:00-17:00 dur:60m every:day".toList,
      "- stretch win:14:00-19:00 dur:30m every:day".toList,
      "- lapsed win:11:30-13:30 dur:30m every:day".toList]⟩]

set_option maxRecDepth 100000 in
theorem the_routine_witness_loads : loadsOk routineWitness = true := by decide

/-- The loaded plan.  Total by `the_routine_witness_loads`: the error branch is refuted, not
defaulted (`Boundary.lookWallPlan`'s pattern). -/
def routinePlan : WfPlan :=
  match h : loadPlan routineWitness with
  | .ok p => p
  | .error _ => absurd the_routine_witness_loads (by simp [loadsOk, h])

set_option maxRecDepth 100000 in
/-- **Three routine lines and the meeting, and the calendar still indexes exactly the one wall**
— so this request's `PlanReq.wallsAgree` is the one `theRequest` has, and a `win:` line is not
a wall. -/
theorem the_routine_witness_holds_three_routines_and_the_wall :
    routinePlan.val.store.dom
        = [['l','a','p','s','e','d'], ['s','t','r','e','t','c','h'], ['w','a','r','m','u','p'],
           ['g','1']] ∧
      Look.wallIndex Cal.chicago 60 routinePlan.val = Look.wednesdayWall := by
  refine ⟨by decide, by decide⟩

/-- `loadsOk`'s shape for `Planner.mkRoutines?`. -/
def routinesOk (p : PlanCore) (xs : List RoutineIn) : Bool :=
  match mkRoutines? p xs with | .ok _ => true | .error _ => false

/-- The two instances the host sends: the mandatory anchor and the one that will be deferred. -/
def routineIns : List RoutineIn :=
  [⟨['w','a','r','m','u','p'], none, (Cal.instantOf Cal.chicago 739867 960).sec,
      (Cal.instantOf Cal.chicago 739867 1020).sec, 60, true⟩,
   ⟨['s','t','r','e','t','c','h'], none, (Cal.instantOf Cal.chicago 739867 840).sec,
      (Cal.instantOf Cal.chicago 739867 1140).sec, 30, false⟩]

set_option maxRecDepth 100000 in
/-- **R10 accepts both** — each names an item its plan holds, each declares a window, neither is
empty and neither is past the horizon (`Planner.mkRoutine?`'s five refusals, none of them
fired). -/
theorem the_routine_instances_are_accepted : routinesOk routinePlan.val routineIns = true := by
  decide

/-- The bounded list, as the decoder built it. -/
def routineCap : Capped RoutineIn :=
  match h : mkRoutines? routinePlan.val routineIns with
  | .ok c => c
  | .error _ => absurd the_routine_instances_are_accepted (by simp [routinesOk, h])

/-- §4.3's Wednesday at 14:00 with two window instances on it. -/
def theRoutineRequest : PlanReq := { theRequest with plan := routinePlan, routines := routineCap }

set_option maxRecDepth 100000 in
/-- **Step 2, computed** — the mandatory instance takes the earliest feasible position inside
its own window and the other is deferred to step 6 with no position at all.  This is the
subject `Planner.a_placed_routine_is_inside_its_window` and every other step-two law has never
had. -/
theorem the_mandatory_routine_is_placed_and_the_other_is_deferred :
    theRoutineRequest.placedRoutines.map (fun q => (q.inst.id, q.placedAt, q.deferred))
      = [(['w','a','r','m','u','p'],
          some ((Cal.instantOf Cal.chicago 739867 960).sec,
                (Cal.instantOf Cal.chicago 739867 1020).sec), false),
         (['s','t','r','e','t','c','h'], none, true)] := by
  decide

set_option maxRecDepth 100000 in
/-- **The two stretches the deferred instance may take, and their energies** — 14:00 at level 4
and 17:00 at level 2, so the rule under test is the only thing that can decide between them. -/
theorem the_deferred_windows_two_stretches_are_at_different_energies :
    Look.freeIntervals (Cal.instantOf Cal.chicago 739867 840).sec
        (Cal.instantOf Cal.chicago 739867 1140).sec
        [((Cal.instantOf Cal.chicago 739867 960).sec,
          (Cal.instantOf Cal.chicago 739867 1020).sec)]
      = [((Cal.instantOf Cal.chicago 739867 840).sec,
          (Cal.instantOf Cal.chicago 739867 960).sec),
         ((Cal.instantOf Cal.chicago 739867 1020).sec,
          (Cal.instantOf Cal.chicago 739867 1140).sec)] ∧
    (Look.todayEnergy theRoutineRequest.look
        ⟨(Cal.instantOf Cal.chicago 739867 840).sec, 0⟩).val = 4 ∧
    (Look.todayEnergy theRoutineRequest.look
        ⟨(Cal.instantOf Cal.chicago 739867 1020).sec, 0⟩).val = 2 := by
  refine ⟨by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- **The two rules disagree at these very arguments.**  Step 2's `Planner.earliestFree` answers
14:00; step 6's `Planner.PlanReq.lowestFree` answers 17:00, two hours later and two levels
lower.  Without this pair the end-to-end placement below would be consistent with step 6 having
no rule of its own. -/
theorem the_lowest_energy_rule_and_the_earliest_rule_disagree_here :
    theRoutineRequest.lowestFree
        [((Cal.instantOf Cal.chicago 739867 960).sec,
          (Cal.instantOf Cal.chicago 739867 1020).sec)]
        (Cal.instantOf Cal.chicago 739867 840).sec
        (Cal.instantOf Cal.chicago 739867 1140).sec 1800
      = some (Cal.instantOf Cal.chicago 739867 1020).sec ∧
    earliestFree (Cal.instantOf Cal.chicago 739867 840).sec
        (Cal.instantOf Cal.chicago 739867 1140).sec 1800
        [((Cal.instantOf Cal.chicago 739867 960).sec,
          (Cal.instantOf Cal.chicago 739867 1020).sec)]
      = some (Cal.instantOf Cal.chicago 739867 840).sec := by
  refine ⟨by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- **And a tie goes to the earlier position** — design §2's choice 6's own parenthesis.  Both
stretches here start at level 3, so the energy decides nothing and the second key does. -/
theorem a_tie_on_energy_goes_to_the_earlier_position :
    (Look.todayEnergy theRoutineRequest.look
        ⟨(Cal.instantOf Cal.chicago 739867 860).sec, 0⟩).val = 3 ∧
    (Look.todayEnergy theRoutineRequest.look
        ⟨(Cal.instantOf Cal.chicago 739867 960).sec, 0⟩).val = 3 ∧
    theRoutineRequest.lowestFree
        [((Cal.instantOf Cal.chicago 739867 900).sec,
          (Cal.instantOf Cal.chicago 739867 960).sec)]
        (Cal.instantOf Cal.chicago 739867 860).sec
        (Cal.instantOf Cal.chicago 739867 1140).sec 1800
      = some (Cal.instantOf Cal.chicago 739867 860).sec := by
  refine ⟨by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- **End to end: the routine that missed its window gets a place.**  `warmup` is where step 2
put it and step 6 did not move it; `stretch` is at 17:00–17:30, marked `deferred`, and nothing
is owed to the notes. -/
theorem the_deferred_routine_takes_the_lowest_energy_position :
    theRoutineRequest.finalRoutines.map (fun q => (q.inst.id, q.placedAt, q.deferred))
      = [(['w','a','r','m','u','p'],
          some ((Cal.instantOf Cal.chicago 739867 960).sec,
                (Cal.instantOf Cal.chicago 739867 1020).sec), false),
         (['s','t','r','e','t','c','h'],
          some ((Cal.instantOf Cal.chicago 739867 1020).sec,
                (Cal.instantOf Cal.chicago 739867 1050).sec), true)] ∧
    theRoutineRequest.noPositionNotes = [] := by
  refine ⟨by decide, by decide⟩

/-- The same two instances, with **one field changed**: `stretch` asks for 150 minutes and not
for 30.  Neither free stretch is that wide. -/
def crowdedIns : List RoutineIn :=
  [⟨['w','a','r','m','u','p'], none, (Cal.instantOf Cal.chicago 739867 960).sec,
      (Cal.instantOf Cal.chicago 739867 1020).sec, 60, true⟩,
   ⟨['s','t','r','e','t','c','h'], none, (Cal.instantOf Cal.chicago 739867 840).sec,
      (Cal.instantOf Cal.chicago 739867 1140).sec, 150, false⟩]

set_option maxRecDepth 100000 in
theorem the_crowded_instances_are_accepted : routinesOk routinePlan.val crowdedIns = true := by
  decide

def crowdedCap : Capped RoutineIn :=
  match h : mkRoutines? routinePlan.val crowdedIns with
  | .ok c => c
  | .error _ => absurd the_crowded_instances_are_accepted (by simp [routinesOk, h])

def theCrowdedRequest : PlanReq := { theRoutineRequest with routines := crowdedCap }

set_option maxRecDepth 100000 in
/-- **A day with no room says so** — fork `run()`'s un-placed note (`planner.rs:1046`), *"a day
that quietly loses lunch is a day no monitor can see"*.  The only difference from the request
above is the minutes asked for. -/
theorem an_instance_with_no_room_is_named_in_the_notes :
    theCrowdedRequest.finalRoutines.map (fun q => (q.inst.id, q.placedAt))
      = [(['w','a','r','m','u','p'],
          some ((Cal.instantOf Cal.chicago 739867 960).sec,
                (Cal.instantOf Cal.chicago 739867 1020).sec)),
         (['s','t','r','e','t','c','h'], none)] ∧
    theCrowdedRequest.noPositionNotes
      = [Note.noPosition ['s','t','r','e','t','c','h'] 150
           (Cal.instantOf Cal.chicago 739867 840).sec
           (Cal.instantOf Cal.chicago 739867 1140).sec] := by
  refine ⟨by decide, by decide⟩

/-- The mandatory anchor and a **carried** instance whose line's daily hours are 11:30–13:30:
its span comes back inverted, which is §5.3's expiry. -/
def lapsedIns : List RoutineIn :=
  [⟨['w','a','r','m','u','p'], none, (Cal.instantOf Cal.chicago 739867 960).sec,
      (Cal.instantOf Cal.chicago 739867 1020).sec, 60, true⟩,
   ⟨['l','a','p','s','e','d'], none, (Cal.instantOf Cal.chicago 739867 900).sec,
      (Cal.instantOf Cal.chicago 739867 960).sec, 30, false⟩]

set_option maxRecDepth 100000 in
theorem the_lapsed_instances_are_accepted : routinesOk routinePlan.val lapsedIns = true := by
  decide

def lapsedCap : Capped RoutineIn :=
  match h : mkRoutines? routinePlan.val lapsedIns with
  | .ok c => c
  | .error _ => absurd the_lapsed_instances_are_accepted (by simp [routinesOk, h])

def theLapsedRequest : PlanReq := { theRoutineRequest with routines := lapsedCap }

set_option maxRecDepth 100000 in
/-- **A window that has closed is passed over and is not reported.**  The span really is
inverted — 15:00 to 13:30 — and `Planner.PlanReq.deferOne_places_nothing_in_a_closed_window` is
the theorem that says nothing is squeezed into it; this is the request where that theorem's
hypothesis holds, and the empty note list is the other half: an expired chance is not a
placement failure. -/
theorem an_instance_whose_window_has_closed_is_passed_over_and_not_reported :
    theLapsedRequest.routineInstances.map (fun q => (q.inst.id, q.span))
      = [(['w','a','r','m','u','p'],
          ((Cal.instantOf Cal.chicago 739867 960).sec,
           (Cal.instantOf Cal.chicago 739867 1020).sec)),
         (['l','a','p','s','e','d'],
          ((Cal.instantOf Cal.chicago 739867 900).sec,
           (Cal.instantOf Cal.chicago 739867 810).sec))] ∧
    theLapsedRequest.finalRoutines.map (fun q => (q.inst.id, q.placedAt))
      = [(['w','a','r','m','u','p'],
          some ((Cal.instantOf Cal.chicago 739867 960).sec,
                (Cal.instantOf Cal.chicago 739867 1020).sec)),
         (['l','a','p','s','e','d'], none)] ∧
    theLapsedRequest.noPositionNotes = [] := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### The displacement, at its own arguments (README gap 903)

`Planner.PlanReq.victimSlot`, `Planner.unspend` and `Planner.PlanReq.rePlaceWalk` are ported
from fork `place_deferred`'s last paragraph and **no request reaches them** — the argument is in
this section's header and in README gap 903.  A definition no input reaches is a definition no
mutation can break (README gap 875's lesson, from the other side), so each is computed here at
its own arguments over the day `theRequest` really produces: four slots at levels **3, 3, 2,
2**. -/

/-- A day whose four slots all went to a group, in the cursor's own vector shape. -/
def theFullDay : Assign := ⟨[some 0, some 1, some 2, some 3], [], 4⟩

set_option maxRecDepth 100000 in
/-- **The victim is the lowest-energy assigned slot, and the latest of those** — fork
`place_deferred`'s own comparator (`planner.rs:1682`), each key isolated.  Over the whole afternoon
the answer is slot **3** (level 2, the later of the two); restricted to the window that ends at
16:20 only the two level-3 slots remain and the answer is slot **1**, the later of *those*;
restricted to a window that starts at 15:00 slot 0 drops out and the answer is 3 again;
restricted to one that ends at 18:00 slot 3 drops out and the answer is **2**; asked for 90
minutes nothing is wide enough; and with a single slot assigned the answer is that slot whatever
its energy. -/
theorem the_victim_is_the_lowest_energy_slot_and_the_latest_of_those :
    theRequest.energisedSlots.map (fun p => p.1.val) = [3, 3, 2, 2] ∧
    theRequest.victimSlot theFullDay (Cal.instantOf Cal.chicago 739867 840).sec
        (Cal.instantOf Cal.chicago 739867 1140).sec 3600 = some 3 ∧
    theRequest.victimSlot theFullDay (Cal.instantOf Cal.chicago 739867 840).sec
        (Cal.instantOf Cal.chicago 739867 980).sec 3600 = some 1 ∧
    theRequest.victimSlot theFullDay (Cal.instantOf Cal.chicago 739867 900).sec
        (Cal.instantOf Cal.chicago 739867 1140).sec 3600 = some 3 ∧
    theRequest.victimSlot theFullDay (Cal.instantOf Cal.chicago 739867 840).sec
        (Cal.instantOf Cal.chicago 739867 1080).sec 3600 = some 2 ∧
    theRequest.victimSlot theFullDay (Cal.instantOf Cal.chicago 739867 840).sec
        (Cal.instantOf Cal.chicago 739867 1140).sec 5400 = none ∧
    theRequest.victimSlot ⟨[some 0, none, none, none], [], 1⟩
        (Cal.instantOf Cal.chicago 739867 840).sec
        (Cal.instantOf Cal.chicago 739867 1140).sec 3600 = some 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- **The restore is exact and local** — fork `groups[gi].left_min += slots[vi].minutes()`.  The
cursor's own day at `theCursorRequest` leaves group 0 with 60 minutes spent against a 60-minute
commitment; giving that slot back takes it to 0 and leaves the other three untouched. -/
theorem the_restore_lowers_one_groups_spent_and_touches_no_other :
    theCursorRequest.assignFold.groups.map (fun g => (g.commitMin, g.spent))
      = [(60, 60), (60, 0), (60, 0), (240, 180)] ∧
    (unspend 0 60 theCursorRequest.assignFold.groups).map (fun g => (g.commitMin, g.spent))
      = [(60, 0), (60, 0), (60, 0), (240, 180)] := by
  refine ⟨by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- **The re-placement is the cursor stopped at its first success**, and here is the difference
computed: from the same empty start, `Planner.PlanReq.assignFold` fills all four slots and
`Planner.PlanReq.rePlaceWalk` fills exactly **one**.  Started after the first slot it fills the
second and stops there — which is fork `place_deferred`'s `break` and the whole of why the
re-placement is not simply the fold run again. -/
theorem the_re_placement_fills_one_slot_where_the_cursor_fills_four :
    theCursorRequest.assignFold.slotOf = [some 0, some 3, some 3, some 3] ∧
    (theCursorRequest.rePlaceWalk (remainingBudget theCursorRequest)
        theCursorRequest.assignStart theCursorRequest.energisedSlots.zipIdx).slotOf
      = [some 0, none, none, none] ∧
    (theCursorRequest.rePlaceWalk (remainingBudget theCursorRequest)
        theCursorRequest.assignStart (theCursorRequest.energisedSlots.zipIdx.drop 1)).slotOf
      = [none, some 0, none, none] := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### Step 6 against a day the cursor filled

The requests above carry no candidate, so `Planner.PlanReq.assignFold` assigns nothing and both
`Planner.PlanReq.assignedSpans` and `Planner.PlanReq.keptBreaksToday` are empty — which would
make two of this step's definitions unfalsifiable here.  This request is the same afternoon with
§8.2 step 5's own four candidates on it (`witCursorCands`), and it is the one where the day runs
out of room: the cursor takes all four slots, the break the morning's log made the cut insert is
**kept** because work touches it, and the 20 minutes before the first slot are the only free
time left — which is the break, so `stretch` has nowhere to go and is named in the notes. -/

def busyIns : List RoutineIn :=
  [⟨['w','a','r','m','u','p'], none, (Cal.instantOf Cal.chicago 739867 960).sec,
      (Cal.instantOf Cal.chicago 739867 1020).sec, 60, true⟩,
   ⟨['s','t','r','e','t','c','h'], none, (Cal.instantOf Cal.chicago 739867 840).sec,
      (Cal.instantOf Cal.chicago 739867 1140).sec, 20, false⟩]

set_option maxRecDepth 100000 in
theorem the_busy_instances_are_accepted : routinesOk routinePlan.val busyIns = true := by decide

def busyCap : Capped RoutineIn :=
  match h : mkRoutines? routinePlan.val busyIns with
  | .ok c => c
  | .error _ => absurd the_busy_instances_are_accepted (by simp [routinesOk, h])

def busyCands : Capped (Look.Cand × Option Look.Floor) := ⟨witCursorCands, by decide⟩

/-- The routine day with §8.2 step 5's four candidates on it. -/
def theBusyRequest : PlanReq :=
  { theRoutineRequest with cands := busyCands, routines := busyCap }

set_option maxRecDepth 100000 in
/-- **A day the cursor filled has nothing left for the routine that missed its window.**  The
four slots go to groups 0 and 3; their spans are what
`Planner.PlanReq.assignedSpans` reports; the 14:00–14:20 break is **kept**, because the slot
that starts at 14:20 touches it; and between them they cover every second of the window, so
`stretch` gets no position and is named. -/
theorem a_day_the_cursor_filled_leaves_the_routine_nowhere_to_go :
    theBusyRequest.assignFold.slotOf = [some 0, some 3, some 3, some 3] ∧
    theBusyRequest.assignedSpans theBusyRequest.assignFold
      = [((Cal.instantOf Cal.chicago 739867 860).sec,
          (Cal.instantOf Cal.chicago 739867 920).sec),
         ((Cal.instantOf Cal.chicago 739867 920).sec,
          (Cal.instantOf Cal.chicago 739867 960).sec),
         ((Cal.instantOf Cal.chicago 739867 1020).sec,
          (Cal.instantOf Cal.chicago 739867 1080).sec),
         ((Cal.instantOf Cal.chicago 739867 1080).sec,
          (Cal.instantOf Cal.chicago 739867 1140).sec)] ∧
    theBusyRequest.keptBreaksToday
      = [((Cal.instantOf Cal.chicago 739867 840).sec,
          (Cal.instantOf Cal.chicago 739867 860).sec)] ∧
    Look.freeIntervals (Cal.instantOf Cal.chicago 739867 840).sec
        (Cal.instantOf Cal.chicago 739867 1140).sec
        (theBusyRequest.occupiedNow theBusyRequest.placedRoutines theBusyRequest.assignFold ++
          theBusyRequest.keptBreaksToday ++ [theBusyRequest.night]) = [] ∧
    theBusyRequest.finalRoutines.map (fun q => (q.inst.id, q.placedAt))
      = [(['w','a','r','m','u','p'],
          some ((Cal.instantOf Cal.chicago 739867 960).sec,
                (Cal.instantOf Cal.chicago 739867 1020).sec)),
         (['s','t','r','e','t','c','h'], none)] ∧
    theBusyRequest.noPositionNotes
      = [Note.noPosition ['s','t','r','e','t','c','h'] 20
           (Cal.instantOf Cal.chicago 739867 840).sec
           (Cal.instantOf Cal.chicago 739867 1140).sec] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- **And each of the two halves is what does it.**  Take the kept break out and the 20 minutes
before the first slot are free — exactly the 20 this instance asks for, so it would be placed
*on the break*.  Take the filled slots out — `Planner.PlanReq.occupiedNow` at the *start* of the
cursor's walk rather than at its end — and two stretches of the afternoon are free and the
instance would take the lower-energy one.  Neither is a hypothetical the day avoids by luck. -/
theorem the_kept_break_and_the_filled_slots_are_each_what_leaves_no_room :
    Look.freeIntervals (Cal.instantOf Cal.chicago 739867 840).sec
        (Cal.instantOf Cal.chicago 739867 1140).sec
        (theBusyRequest.occupiedNow theBusyRequest.placedRoutines theBusyRequest.assignFold ++
          [theBusyRequest.night])
      = [((Cal.instantOf Cal.chicago 739867 840).sec,
          (Cal.instantOf Cal.chicago 739867 860).sec)] ∧
    theBusyRequest.lowestFree
        (theBusyRequest.occupiedNow theBusyRequest.placedRoutines theBusyRequest.assignFold ++
          [theBusyRequest.night])
        (Cal.instantOf Cal.chicago 739867 840).sec
        (Cal.instantOf Cal.chicago 739867 1140).sec 1200
      = some (Cal.instantOf Cal.chicago 739867 840).sec ∧
    Look.freeIntervals (Cal.instantOf Cal.chicago 739867 840).sec
        (Cal.instantOf Cal.chicago 739867 1140).sec
        (theBusyRequest.occupiedNow theBusyRequest.placedRoutines theBusyRequest.assignStart ++
          theBusyRequest.keptBreaksToday ++ [theBusyRequest.night])
      = [((Cal.instantOf Cal.chicago 739867 860).sec,
          (Cal.instantOf Cal.chicago 739867 960).sec),
         ((Cal.instantOf Cal.chicago 739867 1020).sec,
          (Cal.instantOf Cal.chicago 739867 1140).sec)] := by
  refine ⟨by decide, by decide, by decide⟩

/-- An instance with nothing on it but the minutes it asks for: the displacement below reads
only those, and never anything else about the routine. -/
def aBareInstance : Placed := ⟨⟨['x'], none, 0, 1, 30, false⟩, (0, 1), none, false⟩

/-- §8.2 step 5's second slot at `theCursorRequest`, written out. -/
def theSecondSlot : Look.Slot :=
  ⟨(Cal.instantOf Cal.chicago 739867 920).sec, (Cal.instantOf Cal.chicago 739867 980).sec,
   Look.SlotKind.block⟩

set_option maxRecDepth 100000 in
/-- **The displacement, computed at its own arguments** (README gap 903: no request reaches it).
The cursor's day at `theCursorRequest` gives all four slots away and spends four blocks; taking
the second slot back frees exactly that entry, gives the group that held it its 60 minutes back
— 180 spent becomes 120, and no other group moves — costs the day one block, and puts the
instance at the slot's own start for the minutes it asked for.  The re-placement finds nothing,
because every later slot is still taken; `the_re_placement_fills_one_slot_where_the_cursor_fills_four`
is the half where it does fire. -/
theorem the_displacement_frees_one_slot_and_gives_its_minutes_back :
    theCursorRequest.assignFold.used = 4 ∧
    (theCursorRequest.displaceInto (remainingBudget theCursorRequest)
        theCursorRequest.assignFold aBareInstance 1 theSecondSlot).2.slotOf
      = [some 0, none, some 3, some 3] ∧
    (theCursorRequest.displaceInto (remainingBudget theCursorRequest)
        theCursorRequest.assignFold aBareInstance 1 theSecondSlot).2.used = 3 ∧
    (theCursorRequest.displaceInto (remainingBudget theCursorRequest)
        theCursorRequest.assignFold aBareInstance 1 theSecondSlot).2.groups.map
        (fun g => (g.commitMin, g.spent)) = [(60, 60), (60, 0), (60, 0), (240, 120)] ∧
    (theCursorRequest.displaceInto (remainingBudget theCursorRequest)
        theCursorRequest.assignFold aBareInstance 1 theSecondSlot).1.placedAt
      = some ((Cal.instantOf Cal.chicago 739867 920).sec,
              (Cal.instantOf Cal.chicago 739867 950).sec) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ### The day, with step 6 in it

`dayRows` reads `Planner.PlanReq.finalRoutines` rather than
`Planner.PlanReq.placedRoutines`, which is where fork `emit_segments` reads its routines from
(`planner.rs:1032` calls `place_deferred` and `planner.rs:1063` renders after it).  These two
theorems are what that buys, computed on the day above and on the day with no room. -/

set_option maxRecDepth 100000 in
/-- **The day a routine that missed its window is on.**  Seven rows: the morning's two replayed
blocks, the written wall, the mandatory routine where step 2 put it, **the deferred routine at
17:00–17:30 carrying `deferred`**, and §16's evening.  The row is marked, so a reader can see
that the planner put it there and the day did not. -/
theorem the_day_carries_the_deferred_routines_row :
    (dayPlan theRoutineRequest).segments.map
        (fun s => (s.val.start, s.val.stop, s.val.kind, s.val.item))
      = [((Cal.instantOf Cal.chicago 739867 425).sec,
          (Cal.instantOf Cal.chicago 739867 485).sec, SegKind.block, some ['m','1']),
         ((Cal.instantOf Cal.chicago 739867 545).sec,
          (Cal.instantOf Cal.chicago 739867 605).sec, SegKind.block, some ['m','2']),
         ((Cal.instantOf Cal.chicago 739867 770).sec,
          (Cal.instantOf Cal.chicago 739867 830).sec, SegKind.wall, some ['g','1']),
         ((Cal.instantOf Cal.chicago 739867 960).sec,
          (Cal.instantOf Cal.chicago 739867 1020).sec, SegKind.routine,
          some ['w','a','r','m','u','p']),
         ((Cal.instantOf Cal.chicago 739867 1020).sec,
          (Cal.instantOf Cal.chicago 739867 1050).sec, SegKind.routine,
          some ['s','t','r','e','t','c','h']),
         ((Cal.instantOf Cal.chicago 739867 1290).sec,
          (Cal.instantOf Cal.chicago 739867 1320).sec, SegKind.windDown, none),
         ((Cal.instantOf Cal.chicago 739867 1320).sec,
          (Cal.instantOf Cal.chicago 739868 0).sec, SegKind.sleep, none)] ∧
    (dayPlan theRoutineRequest).segments.map (fun s => s.val.flags.deferred)
      = [false, false, false, false, true, false, false] ∧
    (dayPlan theRoutineRequest).diagnostics.notes.val = [] ∧
    assignedOf (dayPlan theRoutineRequest) = [['m','1'], ['m','2']] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- **And the day that had no room says so.**  The same request with the instance asking for
150 minutes: no Routine row for it, and `Planner.Note.noPosition` in the day's own diagnostics
— *"a day that quietly loses lunch is a day no monitor can see"*.  The assigned set is the
morning's two blocks in both, because a Routine row is not work
(`Planner.assignedOf_dayPlan_drops_the_routine_rows`). -/
theorem the_day_with_no_room_carries_the_note_instead :
    (dayPlan theCrowdedRequest).segments.map (fun s => (s.val.kind, s.val.item))
      = [(SegKind.block, some ['m','1']), (SegKind.block, some ['m','2']),
         (SegKind.wall, some ['g','1']), (SegKind.routine, some ['w','a','r','m','u','p']),
         (SegKind.windDown, none), (SegKind.sleep, none)] ∧
    (dayPlan theCrowdedRequest).diagnostics.notes.val
      = [Note.noPosition ['s','t','r','e','t','c','h'] 150
           (Cal.instantOf Cal.chicago 739867 840).sec
           (Cal.instantOf Cal.chicago 739867 1140).sec] ∧
    assignedOf (dayPlan theCrowdedRequest) = [['m','1'], ['m','2']] := by
  refine ⟨by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- **The battery still passes on a day step 6 put a row in, and NOT ONE of the eleven gained a
subject from it** — the answer to "which of L26's eleven does P6 make provable", measured
rather than asserted: design §6.4 assigns no goal to P6, and this is why.

A Routine row is not a Block (`Planner.routineRows_are_not_blocks`), is not a Wall
(`Planner.routineRows_are_not_walls`), is not work
(`Planner.assignedOf_dayPlan_drops_the_routine_rows`), is not a Break, and carries **no slot
energy**, because `Planner.PlanReq.routineEnergy` answers `none` for a `routines.md` line
(fork `emit_segments`' `scheduled` test: furniture has no `ci`).  So the day the deferred
routine is on has **two** Block rows — the morning's replayed pair — **one** Wall, **two**
Routine rows and **nothing** with a slot energy or a Break; every population the eleven range
over is exactly what it was before step 6 wired in, and the burn-down does not move. -/
theorem the_battery_passes_on_the_day_step_six_filled :
    PlanCheck.planOk permissive theRoutineRequest (dayPlan theRoutineRequest) = true ∧
    PlanCheck.planOk permissive theCrowdedRequest (dayPlan theCrowdedRequest) = true ∧
    PlanCheck.planOk permissive theBusyRequest (dayPlan theBusyRequest) = true ∧
    ((dayPlan theRoutineRequest).segments.filter
        (fun s => decide (s.val.kind = SegKind.block))).length = 2 ∧
    ((dayPlan theRoutineRequest).segments.filter
        (fun s => decide (s.val.kind = SegKind.wall))).length = 1 ∧
    ((dayPlan theRoutineRequest).segments.filter
        (fun s => decide (s.val.kind = SegKind.routine))).length = 2 ∧
    ((dayPlan theRoutineRequest).segments.filter (fun s => s.val.energy.isSome)).length = 0 ∧
    ((dayPlan theRoutineRequest).segments.filter
        (fun s => decide (s.val.kind = SegKind.brk))).length = 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ############################################################################
## 18. The quiet day: TEN of the eleven — and the eleventh is not the fold's fault
############################################################################

W-19 put §6.1's lift at **nine of eleven at every eligibility, over
`PlanCheck.withoutPast`'s day**, and proved the two missing conjuncts false.  This
section is the other axis: the **whole** day, at every eligibility, over the class of
requests whose log holds no Block and whose runtime holds no reservation.  There the
lift reaches **ten** — `PlanCheck.dayPlan_ok_on_a_quiet_day_except_hot` — because
`monotoneInRank`, one of W-19's two refuted comparisons, becomes provable when the day
assigns nothing at all.  **The tenth conjunct is vacuous where it is provable** and
`the_tenth_is_vacuous_where_the_eleventh_bites` computes that: the advance is in proof
coverage, not in how many of the eleven have a subject, which is unchanged.

**And ten is a ceiling there too, for a cause that is not the assign fold's.**
`hotBeforeQueue_is_false_on_a_quiet_day` computes the eleventh as `false` at a request
with an **empty log, nothing running and no candidates** — so no step 5, no choice 5b
reservation and no replayed past is available to blame.  The cause is inside the
checker's own quantifier: `PlanCheck.hotPairOk` ranges `sj` over **every** segment of the
day, so the calendar's Wall row carrying `^g1` is a queue position that the hot `^m1`,
which has no row of its own, has failed to get in front of.

That matters for README gap 850, which offered P5 two repairs and said the step must
name which it takes.  **Neither repair reaches this one.**  An eligibleAt that refuses
a candidate at choice 5b's reservation row does not, because there is no reservation
here; the fold does not, because `^m1` is not a candidate here.  What repairs it is
either an eligibility that answers `false` for an item the plan holds and step 5 never
queues, or a restriction of `sj` to `sj.val.kind.isWork` — a **restatement of one of
L26's eleven**, which AGENTS §3.1 item 3 says ships with its refutation in the step that
owns the row, and §6.3 gives that row to P5.  This step supplies the refutation and
leaves the restatement where the design put it.  README gap 960. -/

def witReqInQuietCensus : PlanReqIn :=
  { witReqIn with docs := censusWitness, lines := [] }

/-- **The census Wednesday with nothing going on**: `censusPlan`'s wall and two ranked
siblings, the same day, the same configuration — and an empty log, `RuntimeIn.empty` and
no candidates.  Every field is one an existing witness already uses; nothing is retyped. -/
def theQuietCensusRequest : PlanReq :=
  ⟨censusPlan, witRun0, witInput, RuntimeIn.empty, Capped.nil, witPrio, Capped.nil, none⟩

/-- **The builder accepts it**, by the four stage equations, as every other request here. -/
theorem witBuildsQuietCensus : mkPlanReq? witReqInQuietCensus = .ok theQuietCensusRequest := by
  obtain ⟨ht, hz, hd, hw, -⟩ := witInput_fields
  unfold mkPlanReq? witReqInQuietCensus witReqIn theQuietCensusRequest
  simp only [censusPlan_loads, witInput_decodes]
  rw [if_neg (by
    rw [hw, hz, hd]
    simp only [Look.DayCfg.shipped, Look.CutCfg.shipped, ne_eq]
    exact not_not_intro the_census_witness_indexes_the_calendars_one_wall.symm)]
  rw [hz, ht, witRun0_resumes]
  simp only [Capped.ofList?_nil, mkRoutines?_of_none]

set_option maxRecDepth 40000 in
/-- **It is quiet, computed**: nothing replayed and nothing running — the two hypotheses
`PlanCheck.dayPlan_ok_on_a_quiet_day_except_hot` adds to `dayPlan_ok_core`'s five. -/
theorem the_quiet_census_request_is_quiet :
    pastRows theQuietCensusRequest = [] ∧ theQuietCensusRequest.activeRun = none := by decide

set_option maxRecDepth 40000 in
/-- **The day it produces**: the calendar's wall and §16's two evening rows.  **No Block
row of any kind** — not a replayed one, because the log is empty, and not choice 5b's
reservation, because nothing is running.  This is what makes the refutation below a
statement about the checker and not about the planner. -/
theorem the_quiet_census_day_is_a_wall_and_an_evening :
    (dayPlan theQuietCensusRequest).segments.map
        (fun s => (s.val.start, s.val.stop, s.val.kind, s.val.item))
      = [((Cal.instantOf Cal.chicago 739867 770).sec,
          (Cal.instantOf Cal.chicago 739867 830).sec, SegKind.wall, some (['g','1'] : Id)),
         ((Cal.instantOf Cal.chicago 739867 1290).sec,
          (Cal.instantOf Cal.chicago 739867 1320).sec, SegKind.windDown, none),
         ((Cal.instantOf Cal.chicago 739867 1320).sec,
          (Cal.instantOf Cal.chicago 739868 0).sec, SegKind.sleep, none)] := by
  decide

set_option maxRecDepth 40000 in
/-- **The eleventh checker is FALSE on a quiet day** — at the permissive eligibility, on a
day with no Block row at all.  `assignedOf` is empty here, so this cannot be repaired by
assigning anything: `hotPairOk`'s conclusion is about **segments**, not about the assigned
set, and the segment that defeats it is a Wall.

**It is not vacuous**: `PlanCheck.hotSubjects` computes the pair the quantifier is about. -/
theorem hotBeforeQueue_is_false_on_a_quiet_day :
    assignedOf (dayPlan theQuietCensusRequest) = [] ∧
      PlanCheck.hotBeforeQueue permissive theQuietCensusRequest
        (dayPlan theQuietCensusRequest) = false ∧
      PlanCheck.hotSubjects permissive theQuietCensusRequest (dayPlan theQuietCensusRequest)
        = [(['m','1'], ['g','1'])] := by
  decide

set_option maxRecDepth 40000 in
/-- **The other ten hold at that same request** — the seven of `checksCore`, `monotoneInRank`
(this step's tenth), and the two whose subject is empty at every request.  Computed at the
same `PlanReq` as the refutation above, so "ten of eleven" is a reading of one day and not an
average over two. -/
theorem the_ten_hold_where_the_eleventh_fails :
    PlanCheck.planOkCore theQuietCensusRequest (dayPlan theQuietCensusRequest) = true ∧
      PlanCheck.monotoneInRank permissive theQuietCensusRequest
        (dayPlan theQuietCensusRequest) = true ∧
      PlanCheck.impossibleKept permissive theQuietCensusRequest
        (dayPlan theQuietCensusRequest) = true ∧
      PlanCheck.batchDoesNotReachPast permissive theQuietCensusRequest
        (dayPlan theQuietCensusRequest) = true := by
  decide

/-- **§6.1's whole `planOk` is refuted on the quiet class** — being quiet is not enough.
The two hypotheses this statement carries are exactly the two the quiet lift adds, and both
are theorems above, so the refutation is of the lift's *residue* and not of a strawman.

It does not subsume `dayPlan_ok_at_every_eligibility_is_refuted`: that one refutes the `∀ el
r` form outright, this one refutes it **under the hypotheses that make ten of the eleven
provable**, which is the statement a reader trying to close the last conjunct needs. -/
theorem a_quiet_day_does_not_pass_the_whole_battery :
    ¬ (∀ (el : PlanCheck.Eligible) (r : PlanReq),
        r.activeRun = none → (∀ t ∈ pastRows r, t.kind ≠ SegKind.block) →
        PlanCheck.planOk el r (dayPlan r) = true) := by
  intro h
  have hq := h permissive theQuietCensusRequest the_quiet_census_request_is_quiet.2
    (by rw [the_quiet_census_request_is_quiet.1]; simp)
  have hhot : PlanCheck.hotBeforeQueue permissive theQuietCensusRequest
      (dayPlan theQuietCensusRequest) = true :=
    PlanCheck.checks_all permissive _ _ hq ⟨.hot, PlanCheck.hotBeforeQueue permissive⟩
      (by simp [PlanCheck.checksOf, PlanCheck.checksEligible])
  rw [hotBeforeQueue_is_false_on_a_quiet_day.2.1] at hhot
  exact absurd hhot (by simp)

/-! ### The quiet lift, fired — every hypothesis a theorem, none assumed

AGENTS §7.4 item 2: a lift with seven hypotheses and no instance is a promise about a domain
nobody has shown to be inhabited.  `theQuietRequest` is that instance.  Its `hplain` is
**`the_running_request_is_plain` itself** — the two requests differ only in `run` and `state`,
neither of which `hplain` reads, so the hypothesis is the same proposition and is not
re-proved (AGENTS §5.3). -/

set_option maxRecDepth 40000 in
theorem the_quiet_request_agrees :
    theQuietRequest.activeAgrees = true ∧ theQuietRequest.dayAgrees = true ∧
      theQuietRequest.now.sec + 1 < LogStamp.yearEnd ∧
      pastRows theQuietRequest = [] ∧ theQuietRequest.activeRun = none := by decide

/-- `hagree`, from the builder. -/
theorem theQuietRequest_wallsAgree : theQuietRequest.wallsAgree = true :=
  mkPlanReq?_ok_wallsAgree witReqIn0 theQuietRequest witBuilds0

set_option maxRecDepth 40000 in
/-- **The ten-of-eleven lift, applied.**  Nothing here is a `decide` on the conclusion. -/
theorem the_quiet_lift_applies_at_the_quiet_request :
    PlanCheck.planOkCore theQuietRequest (dayPlan theQuietRequest) = true ∧
      PlanCheck.monotoneInRank permissive theQuietRequest (dayPlan theQuietRequest) = true ∧
      PlanCheck.impossibleKept permissive theQuietRequest (dayPlan theQuietRequest) = true ∧
      PlanCheck.batchDoesNotReachPast permissive theQuietRequest
        (dayPlan theQuietRequest) = true :=
  PlanCheck.dayPlan_ok_on_a_quiet_day_except_hot permissive theQuietRequest
    theQuietRequest_wallsAgree the_quiet_request_agrees.1 the_quiet_request_agrees.2.1
    the_quiet_request_agrees.2.2.1
    (by rw [the_quiet_request_agrees.2.2.2.1]; simp)
    the_quiet_request_agrees.2.2.2.2 the_running_request_is_plain

set_option maxRecDepth 40000 in
/-- **The whole battery, at one request, from the general lift plus one computed conjunct.**
The one-id store makes `hotBeforeQueue` vacuously true here — `the_one_id_store_gives_neither
_comparison_a_subject` computes that population as empty — so this is `PlanCheck.planOk` over
a day `Planner.dayPlan` really produces, at every field the lift names.  **It is an instance,
not a discharge**: the conjunct that is vacuous here is the one refuted above. -/
theorem the_quiet_battery_passes_at_the_quiet_request :
    PlanCheck.planOk permissive theQuietRequest (dayPlan theQuietRequest) = true :=
  PlanCheck.dayPlan_ok_on_a_quiet_day_given_hot permissive theQuietRequest
    theQuietRequest_wallsAgree the_quiet_request_agrees.1 the_quiet_request_agrees.2.1
    the_quiet_request_agrees.2.2.1
    (by rw [the_quiet_request_agrees.2.2.2.1]; simp)
    the_quiet_request_agrees.2.2.2.2 the_running_request_is_plain
    (by decide)

/-! ### The same lift at the request where the eleventh fails

`theQuietCensusRequest`'s store holds three ids, so `monotoneInRank` and `hotBeforeQueue`
have pairs to range over here and the ten are not ten vacuous conjuncts.  Its `hplain` is
`the_census_request_is_plain` itself: the two requests share `plan`, `tz` and the day, and
differ only in `run` and `state`, neither of which `hplain` reads (AGENTS §5.3). -/

set_option maxRecDepth 40000 in
theorem the_quiet_census_request_agrees :
    theQuietCensusRequest.activeAgrees = true ∧ theQuietCensusRequest.dayAgrees = true ∧
      theQuietCensusRequest.now.sec + 1 < LogStamp.yearEnd := by decide

theorem theQuietCensusRequest_wallsAgree : theQuietCensusRequest.wallsAgree = true :=
  mkPlanReq?_ok_wallsAgree witReqInQuietCensus theQuietCensusRequest witBuildsQuietCensus

set_option maxRecDepth 40000 in
/-- **The ten, from the general lift, at the request where the eleventh is `false`.**  This is
`the_ten_hold_where_the_eleventh_fails` again by a second route: that one computes the four
conjunctions with `decide`, this one derives them from
`PlanCheck.dayPlan_ok_on_a_quiet_day_except_hot`.  What the two together cross-check is the
**lift**, not the day — both evaluate the same `Planner.dayPlan`. -/
theorem the_quiet_lift_applies_at_the_quiet_census_request :
    PlanCheck.planOkCore theQuietCensusRequest (dayPlan theQuietCensusRequest) = true ∧
      PlanCheck.monotoneInRank permissive theQuietCensusRequest
        (dayPlan theQuietCensusRequest) = true ∧
      PlanCheck.impossibleKept permissive theQuietCensusRequest
        (dayPlan theQuietCensusRequest) = true ∧
      PlanCheck.batchDoesNotReachPast permissive theQuietCensusRequest
        (dayPlan theQuietCensusRequest) = true :=
  PlanCheck.dayPlan_ok_on_a_quiet_day_except_hot permissive theQuietCensusRequest
    theQuietCensusRequest_wallsAgree the_quiet_census_request_agrees.1
    the_quiet_census_request_agrees.2.1 the_quiet_census_request_agrees.2.2
    (by rw [the_quiet_census_request_is_quiet.1]; simp)
    the_quiet_census_request_is_quiet.2 the_census_request_is_plain

set_option maxRecDepth 40000 in
/-- **The two comparisons' subject populations at that request, computed** — the census idiom
(README gap 852), and it is the honest limit of the tenth conjunct.

**`monotoneInRank` is VACUOUS here, and that is exactly why it is provable.**
`PlanCheck.rankSubjects` requires `j ∈ assignedOf d`, and `assignedOf` is empty on a quiet
day, so its population is `[]` at this request and at every quiet one:
`PlanCheck.monotoneInRank_of_nothing_assigned` proves the conjunct by proving the quantifier
empty.  W-19's ceiling of nine was over a day with a subject for it; the tenth conjunct this
step adds is a **proof-coverage** advance and not a subject-coverage one, and the count of
checkers with a subject does not move.  Said here rather than left for a reader to infer from
a count.

**`hotBeforeQueue`'s population is not empty** — the pair `(^m1, ^g1)` — which is what makes
its refutation a refutation and not a second empty quantifier. -/
theorem the_tenth_is_vacuous_where_the_eleventh_bites :
    PlanCheck.rankSubjects permissive theQuietCensusRequest (dayPlan theQuietCensusRequest) = [] ∧
      PlanCheck.hotSubjects permissive theQuietCensusRequest (dayPlan theQuietCensusRequest)
        = [(['m','1'], ['g','1'])] := by
  decide

/-! ### README gap 806's two clauses, fired at the cursor's own day

`PlanCheck.the_cursor_refuses_a_group_that_owes_nothing` and
`PlanCheck.the_cursor_refuses_an_atomic_group_whose_run_is_broken` are ∀-theorems over every
accumulator, so they hold at every point of `Planner.PlanReq.assignFold`'s walk; what they
need beside them is a request where the thing they gate really happens, or they are AGENTS
§9.2's *"a check no input can fail"*.  `theCursorRequest` is that request:
`the_cursor_fills_the_day_in_key_order` gives `^c1` the first slot and **nothing** after it,
and the reason is the first clause — `^c1`'s whole commitment went into that one block. -/

set_option maxRecDepth 100000 in
/-- **The clause bites here**: after the walk, `^c1`'s group owes nothing, and the three later
slots went elsewhere.  `PlanCheck.the_cursor_refuses_a_group_that_owes_nothing` is the reason,
and `PlanCheck.assignFold_owes` is the invariant it survives as. -/
theorem the_first_group_is_spent_after_one_slot :
    (theCursorRequest.assignFold.groups.map (fun g => (g.commitMin, g.spent, g.live))).take 1
      = [(60, 60, false)] := by
  decide

set_option maxRecDepth 100000 in
/-- **`PlanCheck.OwesSomething` has a subject at this request** — four slots are taken, so the
invariant is not a statement about an empty assignment. -/
theorem the_owes_invariant_has_a_subject :
    theCursorRequest.assignFold.slotOf = [some 0, some 3, some 3, some 3] := by decide

/-! ############################################################################
## 19. The ratio, computed; and the eleven, at a work-anchored eligibility (W-21)

**One request, one ratio, and the compiler counts it.**  Three runs shipped a sentence of the
form "N of the eleven" and they were counting two different things — W-18's **seven of eleven
with a subject at `theCensusRequest`**, W-19's **nine of eleven conjuncts proved**, W-20's
**ten of eleven on the quiet class**.  `PlanCheck.subjectCount` ends the ambiguity on the
subject side: it filters `PlanCheck.checksOf`'s **own** list on each check's **own** name, so
the count is the compiler's arithmetic over the battery rather than a reader's over a table
beside it.  `the_census_ratio` below is that number at `theCensusRequest` and it is **seven**,
which is what W-18 settled and what every sentence in this repository now says.

**And seven is a ceiling, not a high-water mark.**  `PlanCheck.the_census_ceiling_is_seven`
proves that no `PlanReq` at all can put more than seven of the eleven in play on a day
`Planner.dayPlan` produces, because four of them have an empty subject at **every** request —
design §6.4 gives those four to P5, P5/P7 and P8.  The survey that used to stand for this was
a `#eval` over the module's witnesses; the theorem replaces it.
############################################################################ -/

/-- **An eligibility that admits a candidate only at a row §8.2 step 5 could assign into.**
The most permissive `PlanCheck.WorkAnchored` one: everything, at a Block or a Batch row, and
nothing anywhere else.  Planner.eligibleAt's body is P5's; this is the shape the lift needs
it to have, made concrete so the lift can be fired today. -/
def onlyOnWorkRows : PlanCheck.Eligible := fun _ _ s _ => s.kind.isWork

theorem onlyOnWorkRows_is_work_anchored : PlanCheck.WorkAnchored onlyOnWorkRows :=
  fun _ _ _ _ h => h

set_option maxRecDepth 40000 in
/-- **§6.1's dayPlan_ok at ELEVEN of eleven, fired.**  Nothing here is a `decide` on the
conclusion: `PlanCheck.dayPlan_ok_on_a_quiet_day` is the general theorem and every hypothesis
is a theorem above.  This is the request W-20 left at ten with the eleventh **refuted** at
`permissive` — `hotBeforeQueue_is_false_on_a_quiet_day` — so the two theorems together locate
the residue exactly: it was never the planner's and never the fold's, it was an eligibility
that called a Wall row a queue position. -/
theorem the_whole_battery_passes_on_the_quiet_census_day :
    PlanCheck.planOk onlyOnWorkRows theQuietCensusRequest (dayPlan theQuietCensusRequest)
      = true :=
  PlanCheck.dayPlan_ok_on_a_quiet_day onlyOnWorkRows theQuietCensusRequest
    theQuietCensusRequest_wallsAgree the_quiet_census_request_agrees.1
    the_quiet_census_request_agrees.2.1 the_quiet_census_request_agrees.2.2
    (by rw [the_quiet_census_request_is_quiet.1]; simp)
    the_quiet_census_request_is_quiet.2 the_census_request_is_plain
    onlyOnWorkRows_is_work_anchored

set_option maxRecDepth 40000 in
/-- The same, at the one-id request W-20 fired the ten-of-eleven lift at. -/
theorem the_whole_battery_passes_on_the_quiet_day :
    PlanCheck.planOk onlyOnWorkRows theQuietRequest (dayPlan theQuietRequest) = true :=
  PlanCheck.dayPlan_ok_on_a_quiet_day onlyOnWorkRows theQuietRequest
    theQuietRequest_wallsAgree the_quiet_request_agrees.1 the_quiet_request_agrees.2.1
    the_quiet_request_agrees.2.2.1
    (by rw [the_quiet_request_agrees.2.2.2.1]; simp)
    the_quiet_request_agrees.2.2.2.2 the_running_request_is_plain
    onlyOnWorkRows_is_work_anchored

set_option maxRecDepth 100000 in
/-- **WHAT THE ELEVEN IS WORTH ON A QUIET DAY: one checker.**  The theorem above proves all
eleven conjuncts; this computes how many of them had anything to range over, and the answer is
`wallsUnmoved` and nothing else.  A `WorkAnchored` eligibility admits nothing at all on a day
with no work row (`PlanCheck.eligibleSomewhere_of_no_work_row`), so the four
eligibility-dependent conjuncts go from *one* vacuous (W-20's tenth) to **four**.

That is the honest reading and it is stated here rather than left for a reader to infer from
"eleven of eleven": the advance is that the residue is now a named property of
Planner.eligibleAt instead of a restatement of an L26 goal, **not** that more of the battery
bites. -/
theorem the_quiet_eleven_is_one_checker_biting :
    ((PlanCheck.checksOf onlyOnWorkRows).map (fun c =>
        PlanCheck.subjectOf onlyOnWorkRows c.name theQuietCensusRequest
          (dayPlan theQuietCensusRequest)))
      = [false, false, false, false, false, false, true, false, false, false, false] ∧
    PlanCheck.subjectCount onlyOnWorkRows theQuietCensusRequest
      (dayPlan theQuietCensusRequest) = 1 := by
  decide

set_option maxRecDepth 100000 in
/-- **THE RATIO — one request, one number, computed: SEVEN of the eleven.**  The `Bool` list
is `PlanCheck.checksOf`'s own order — `overbook, oneBlock, energyFilter, overWall, overBreak,
windDown, wallMoved, rank, hot, impossible, batch` — so a reader can see *which* seven without
a table to transcribe, and `PlanCheck.subjectCount` is the same eleven counted by the
compiler.

The four `false`s are `energyFilter`, `windDown`, `impossible` and `batch`, and
`PlanCheck.the_census_ceiling_is_seven` proves those four are `false` at **every** request, so
this seven is the ceiling and it is reached here.  Section 14's table is its prose. -/
theorem the_census_ratio :
    ((PlanCheck.checksOf permissive).map (fun c =>
        PlanCheck.subjectOf permissive c.name theCensusRequest (dayPlan theCensusRequest)))
      = [true, true, false, true, true, false, true, true, true, false, false] ∧
    PlanCheck.subjectCount permissive theCensusRequest (dayPlan theCensusRequest) = 7 := by
  decide

set_option maxRecDepth 100000 in
/-- **The ratio does not depend on the eligibility here.**  `onlyOnWorkRows` is strictly less
permissive than `permissive`, and the census is the same seven — the census day has work rows,
so `PlanCheck.eligibleSomewhere` answers `true` under both.  Stated because
`PlanCheck.planOk_antitone` makes "at every eligibility" a real quantifier now, and a ratio
that moved with `el` would be a ratio that needs one named. -/
theorem the_census_ratio_at_a_work_anchored_eligibility :
    PlanCheck.subjectCount onlyOnWorkRows theCensusRequest (dayPlan theCensusRequest) = 7 := by
  decide

set_option maxRecDepth 100000 in
/-- **§8.2 step 6 gave no checker a subject — as a SET, not as a count.**  The addendum to
P6's block computed that the populations the eleven range over were unchanged by the deferred
pass, row kind by row kind.  This is the same claim in the census's own terms and it is
stronger: the eleven-entry census at `theRoutineRequest` — the first request in this
repository that carries a window instance and the only one whose day holds Routine rows — is
**equal to** the census at `theRunningRequest`, which has none.  Four in both, and the same
four.

**Design §6.4 predicted it** (P6 has no row in that table) and README gap 961 owns the
distinction; what is new is that the prediction is now an equality between two computed
lists. -/
theorem step_six_gave_no_checker_a_subject :
    ((PlanCheck.checksOf permissive).map (fun c =>
        PlanCheck.subjectOf permissive c.name theRoutineRequest (dayPlan theRoutineRequest)))
      = ((PlanCheck.checksOf permissive).map (fun c =>
        PlanCheck.subjectOf permissive c.name theRunningRequest (dayPlan theRunningRequest))) ∧
    PlanCheck.subjectCount permissive theRoutineRequest (dayPlan theRoutineRequest) = 4 ∧
    ((PlanCheck.checksOf permissive).map (fun c =>
        PlanCheck.subjectOf permissive c.name theRoutineRequest (dayPlan theRoutineRequest)))
      = [true, true, false, true, false, false, true, false, false, false, false] := by
  decide

set_option maxRecDepth 100000 in
/-- **The census is not a checker in disguise.**  `PlanCheck.subjectOf` spells antecedents and
never a conclusion, so it must be possible for a checker to have a subject **and fail**.  It
is, and this is the instance: at `theQueuedRequest` both comparisons have a subject and both
are `false` (`the_two_comparisons_are_false_at_the_queued_request`,
`the_two_comparisons_have_subjects_where_they_bite`), and the census there counts **five**.  A
`subjectOf` that had quietly become a checker would have answered `false` for those two. -/
theorem the_census_counts_a_checker_that_fails :
    PlanCheck.subjectCount permissive theQueuedRequest (dayPlan theQueuedRequest) = 5 ∧
      PlanCheck.subjectOf permissive .rank theQueuedRequest (dayPlan theQueuedRequest) = true ∧
      PlanCheck.subjectOf permissive .hot theQueuedRequest (dayPlan theQueuedRequest) = true ∧
      PlanCheck.planOk permissive theQueuedRequest (dayPlan theQueuedRequest) = false := by
  decide

end PlannerWit
end Tm
