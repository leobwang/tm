import TmKernel.Boundary
import TmKernel.PlanCheck
import TmKernel.Recur
/-!
# A `PlanReq` that can be written down, and the four witnesses it unblocks

Stage 6, track W (run W-15).  README **gap 348**: *"no `PlanReq` can be built inside
`Planner.lean`, so the wall laws have no end-to-end witness"* — and the W-14 repair step made
that gap the blocker for three others (366, 393's witness half, 396).  This module is gap 348
item 4's second option, taken by name: *"a small `PlannerWit.lean` importing `Boundary` and
`Planner`"*.  It imports `Boundary` for `loadPlan` and `PlanCheck` for the battery, and
**nothing imports it**, so no shipped path grows.

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
`Planner.the_day_assigns_nothing_after_now_until_the_assign_step_lands`.
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
  /-- `lookaheadOf?` refused the EDF lookahead: a zero denominator, or days out of order. -/
  | caps
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
  /-- The EDF pass's denominator (`Look.capDen` on the shipped path). -/
  den       : Nat
  /-- §9's five rows `Look.Today` does not carry. -/
  state     : RuntimeIn
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
        match lookaheadOf? x.den (Look.lookahead I) with
        | none => .error .caps
        | some la =>
          match mkRoutines? p.val x.routines with
          | .error e => .error (.routines e)
          | .ok rs => .ok ⟨p, run, I, la, x.state, rs, x.overrides⟩

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

theorem mkPlanReq?_refuses_a_zero_denominator (x : PlanReqIn) (p : WfPlan) (I : Look.Input)
    (run : Seal.Run) (hp : loadPlan x.docs = .ok p) (hI : Look.mkInput? x.input = .ok I)
    (hw : I.walls = Look.wallIndex I.tz I.day.cut.blockMin p.val)
    (hr : Seal.resumeRun I.tz I.today (Seal.Ckpt.empty I.tz) x.lines = .ok run)
    (h : x.den = 0) : mkPlanReq? x = .error .caps := by
  simp [mkPlanReq?, hp, hI, hw, hr, h, lookaheadOf?_refuses_a_zero_denominator]

/-- **The routine refusal is reachable and named** (R10, W-15's land step).  The rule is
`Planner.mkRoutine?`'s — this builder only carries its `RoutineErr` out under `WitErr.routines`,
so gap 285's refusal is not dropped between the wire and the request either. -/
theorem mkPlanReq?_refuses_a_routine_the_rule_refuses (x : PlanReqIn) (p : WfPlan)
    (I : Look.Input) (run : Seal.Run) (la : Lookahead) (e : RoutineErr)
    (hp : loadPlan x.docs = .ok p) (hI : Look.mkInput? x.input = .ok I)
    (hw : I.walls = Look.wallIndex I.tz I.day.cut.blockMin p.val)
    (hr : Seal.resumeRun I.tz I.today (Seal.Ckpt.empty I.tz) x.lines = .ok run)
    (hla : lookaheadOf? x.den (Look.lookahead I) = some la)
    (h : mkRoutines? p.val x.routines = .error e) :
    mkPlanReq? x = .error (.routines e) := by
  simp [mkPlanReq?, hp, hI, hw, hr, hla, h]

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
      lookaheadOf? x.den (Look.lookahead r.look) = some r.caps ∧
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
              exact ⟨hp, hI, hr, hla, rfl, hrs, rfl⟩

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

set_option maxRecDepth 40000 in
theorem witCaps_ok : (lookaheadOf? Look.capDen (Look.lookahead witInput)).isSome = true := by
  decide

def witCaps : Lookahead :=
  match h : lookaheadOf? Look.capDen (Look.lookahead witInput) with
  | some la => la
  | none => absurd witCaps_ok (by simp [h])

theorem witCaps_eq : lookaheadOf? Look.capDen (Look.lookahead witInput) = some witCaps := by
  unfold witCaps
  split
  · rename_i la h; rw [h]
  · rename_i h; exact absurd witCaps_ok (by simp [h])

/-- The raw request. -/
def witReqIn : PlanReqIn where
  docs := lookWallWitness
  lines := witLines
  input := witInputIn
  den := Look.capDen
  state := RuntimeIn.empty
  routines := []
  overrides := none

/-- **The request `Planner.lean` could not write down** (README gap 348).  Its routine list
is EMPTY: the witness day is two replayed blocks and the written wall, and P2's placement
adds no row to a day whose host sent no window instance
(`the_witness_carries_no_routine`). -/
def theRequest : PlanReq :=
  ⟨lookWallPlan, witRun, witInput, witCaps, RuntimeIn.empty, Capped.nil, none⟩

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
  simp only [witCaps_eq, mkRoutines?_of_none]

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
/-- **And the set §8.3's laws are about is still empty**, at the same request.
`Planner.the_day_assigns_nothing_after_now_until_the_assign_step_lands` is proved for every
request; this is it fired at one, and it is the tripwire P5 must delete.  The two theorems
together are the distinction the W-14 repair drew: `assignedOf` counts the replayed past,
`assignedFrom … now` counts the planner's own placements, and only the second is empty. -/
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
  ⟨lookWallPlan, witRun0, witInput, witCaps, RuntimeIn.empty, Capped.nil, none⟩

theorem witBuilds0 : mkPlanReq? witReqIn0 = .ok theQuietRequest := by
  obtain ⟨ht, hz, hd, hw, -⟩ := witInput_fields
  unfold mkPlanReq? witReqIn0 witReqIn theQuietRequest
  simp only [lookWallPlan_loads, witInput_decodes]
  rw [if_neg (by
    rw [hw, hz, hd]
    simp only [Look.DayCfg.shipped, Look.CutCfg.shipped, ne_eq]
    exact not_not_intro the_look_wall_calendar_indexes_one_wednesday_wall.symm)]
  rw [hz, ht, witRun0_resumes]
  simp only [witCaps_eq, mkRoutines?_of_none]

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
`Planner.the_day_assigns_nothing_after_now_until_the_assign_step_lands`: the day the fold spends
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
  unfold dayRows stepTwoSegs PlanReq.placedRoutines PlanReq.eveningRows PlanReq.sleepSeg
    PlanReq.sleepInstance
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

end PlannerWit
end Tm
