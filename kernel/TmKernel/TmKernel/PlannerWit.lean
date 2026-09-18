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
def witPrio : PrioCfg := ⟨Look.defaultBinsV, Arith.safety, specDefaultPrio, true⟩

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
  have hs : ∀ l : List Placed,
      splitSleep { r with look := { r.look with today0 := { r.look.today0 with budget := b } } } l
        = splitSleep r l := splitSleep_congr rfl
  unfold assignedOf
  rw [dayPlan_segments, dayPlan_segments]
  unfold dayRows stepTwoSegs PlanReq.placedRoutines PlanReq.placementFold PlanReq.eveningRows
    PlanReq.sleepSeg PlanReq.sleepInstance
  rw [show PlanReq.routineInstances
      { r with look := { r.look with today0 := { r.look.today0 with budget := b } } }
        = r.routineInstances from rfl, hs]
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

/-- §7.4's six: the calendar's own wall `^g1` (the one item `lookWallPlan` holds, so its line
order is a real one), an optional, an overdue instance, a mandatory instance, and two plain
`rank` candidates whose `k` differs — `^r1` carries a written `!1` and `^r2` takes
`default_priority`.  The dated ones carry a placement window, which is what keeps them out of
the pass without making their `due` a lie. -/
def witCands : List (Look.Cand × Option Look.Floor) :=
  [(⟨['g','1'], 3, none,   60, some 739870, false, true,  false, false, false, false, none⟩, none),
   (⟨['o'],     3, none,   20, some 739870, false, false, true,  false, false, false, none⟩, none),
   (⟨['o','d'], 3, none,   30, some 739870, true,  false, false, true,  false, false, none⟩, none),
   (⟨['m'],     3, none,   30, some 739870, true,  false, false, false, true,  false, none⟩, none),
   (⟨['r','1'], 3, some 0, 50, none,        false, false, false, false, false, false, none⟩, none),
   (⟨['r','2'], 3, none,   50, none,        false, false, false, false, false, false, none⟩, none)]

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
  [(⟨['g','1'], 3, none,   60, some 739870, false, true,  false, false, false, false, none⟩, none),
   (⟨['o'],     3, none,   20, some 739870, false, false, true,  false, false, false, none⟩, none),
   (⟨['m'],     3, none,   30, some 739870, true,  false, false, false, true,  false, none⟩, none),
   (⟨['o','d'], 3, none,   30, some 739870, true,  false, false, true,  false, false, none⟩, none),
   (⟨['r','1'], 3, some 0, 50, none,        false, false, false, false, false, false, none⟩, none),
   (⟨['r','2'], 3, none,   50, none,        false, false, false, false, false, false, none⟩, none)]

/-- **And the request position is a real tie-break, not decoration**: swap the two `p = 0`
candidates on the wire and the order swaps with them.  Two candidates that agree on every key
component but their arrival order are exactly §5.3's carried instance and today's fresh one. -/
theorem the_request_order_breaks_a_tie :
    rankedIds { theRankingRequest with cands := ⟨witCandsSwapped, by decide⟩ } =
      [['g','1'], ['m'], ['o','d'], ['r','1'], ['o'], ['r','2']] := by
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
  not, and each of the six waits on a named later step.  (This read *"six … and five do not"*
  until the W-17 repair: it counted `wallsUnmoved`, whose subject is there at `theRequest` and
  at `theRunningRequest` but **not** at the request the census is stated over — the caveat the
  table carried and the count did not.  The census now computes that conjunct too.)
* **Bites** — some mutation of that same produced day is refused.  `the_battery_bites_*`
  below, with W-15's and W-16's, make it **eleven of eleven**.

**No second copy of any placement rule is written here** (AGENTS §5.3, and the W-14 land step's
own refusal): every mutation is a `List.map` or `List.filter` over the day
`Planner.dayPlan` built, and every verdict is `PlanCheck`'s own checker evaluating. -/

/-- **A store that holds the ids the morning actually worked.**  `Boundary.lookWallPlan` is a
one-line calendar, so `effectiveCi` answers §3.1's default of three for the replayed rows'
`m1`/`m2` and the store has **one** id in it — which leaves five of the eleven checkers with
nothing to range over for reasons that are about the *witness* and not about the *planner*.

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
`Planner.eligibleAt` (README gap 365).  It is named once here rather than spelled at each use,
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
* **no Break row** — `noBlockOverABreak` is vacuous; the cut's breaks reach the day only when
  work touches them (`Planner.a_break_row_is_a_replayed_row`, README gap 551), which is **P5**;
* **no row carries a slot energy** — `energyFilterOk` is vacuous; a Block gets one when the
  assign fold puts it in an energised slot, which is **P5**;
* **no Block at or after the wind-down** — `noDemandingAfterWindDown` is vacuous; **P5/P7**;
* **no Batch row** — `batchDoesNotReachPast` is vacuous; **P5**;
* **`diagnostics.impossible` is empty** — `impossibleKept` is vacuous; **P8**, the step that
  fills it (gap 367's second half; its first landed at P4 as `Planner.edfNumbers`, and this
  line read "**P4**" until the W-17 repair — P4 landed without ending it);
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
paragraph names; that paragraph cited `the_battery_census_at_the_reserved_day` before the
theorem existed.

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
  [(⟨['m','1'], 3, none, 50, none, false, false, false, false, false, false, none⟩, none),
   (⟨['m','2'], 3, none, 50, none, false, false, false, false, false, false, none⟩, none)]

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
it, which is design §6.3 row 1 taken literally — **three of seven**. -/
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

end PlannerWit
end Tm
