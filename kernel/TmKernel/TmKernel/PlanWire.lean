import TmKernel.EmitWire
/-!
# `PlanWire.lean` — the PLANNER's inputs cross the wire (stage 6, W-27, D48, README gaps 1431/801)

W-24's `EmitWire.lean` put an `Emit.Row` on the wire and said, in its own header, that the
planner's inputs *"belong with step R3, where `tm-core/src/planner.rs` dies"*.  W-25 doing R2
found the cycle that makes that impossible — aiming `tm/tests/planner_invariants.rs` at the
kernel needs `Planner.dayPlan` reachable through the FFI, and that wire was R3's, and R3
depends on R2 (README gap **1431**).  **D48 moved the wire into R2 and left R3 the deletion.**
This module is the request half of that move.

## What crosses here, and what was already on the wire

`Planner.PlanReq` has eight fields.  **Four of them were already carried** and this module does
not read any of them a second time (AGENTS §5.3):

| `PlanReq` field | already on the wire as | read by |
|---|---|---|
| `plan` | the request's `docs` | `Boundary.runLoad` → `Boundary.loadPlan` |
| `run` | the `log` section, since K1's seam (D24) | `Boundary.readLogReq` → `Boundary.logLines` |
| `look` | the `capacity` section | `CapWire.readCapacityZ` → `Look.mkInput?` |
| `cands` | `capacity.candidates.items` | `Boundary.readCandFloor` |

and `prio`'s first four (`bins`, `safety`, `dflt`, `hyst`) are `CapReq.bins`/`safety`/`dflt`
and `CandReq.hysteresis`, which the capacity section already decodes.

**Four values were on no wire at all**, and they are this module's subject: `state` (§9's
`RuntimeIn`), `routines` (`Capped RoutineIn`), `overrides` (`Option PlanOverrides`) and
`prio.batchMaxMin` (§16's `[priority] batch_max_min`, whose R10 statement has been owed since
stage 5 as README gap **801**).

## R10's table for this section — and every bound is one this wire already carries

**No number is minted here.**  Gap **1330** is the standing warning: `CapWire.maxCandidates`
and `Planner.maxCands` are already one number under two names, found at W-24 and not fixed, and
a third name for a bound is the defect this kernel is named after.

| wire value | bound | constructor | rejection theorem |
|---|---|---|---|
| every id (`active.id`, `interrupt.id`, a routine's `id` and `inst`, an override's id, a `yesterday` id) | `CapWire.maxCandId` | `EmitWire.idWithin` | `readActive_refuses_a_long_id`, `readInterrupt_refuses_a_long_id`, `readRoutine_refuses_a_long_id`, `readOverrides_refuses_a_long_drop_id` |
| `active.estMin` | `Look.maxDayMin`, through the wf predicate | `Planner.mkActive?` | `readActive_refuses_an_estimate_past_the_day` |
| `active.started`, `brk.started`, `interrupt.started`, a routine's `winLo`/`winHi` | `Cal.Instant.wf` | `Cal.mkInstant?`, through `EmitWire.secWithin` | `instantWithin_refuses_past_the_calendar`, `readRoutine_refuses_a_window_past_the_calendar` |
| `active.started ≤ now` | `Planner.ActiveBlock.wf` | `Planner.mkActive?` | `readActive_refuses_a_start_after_now` |
| `brk.plannedMin` | `Look.maxDayMin`, through the wf predicate | `Planner.mkBreak?` | `readBreak_refuses_a_break_longer_than_a_day` |
| `brk.started ≤ now` | `Planner.BreakState.wf` | `Planner.mkBreak?` | `readBreak_refuses_a_start_after_now` |
| `interrupt.started ≤ now` | `Planner.InterruptState.wf` | `Planner.mkInterrupt?` | `readInterrupt_refuses_a_start_after_now` |
| `lastHash` | `Planner.hashBound`, exactly `hashHexLen` hex digits | `Planner.mkHash?` | `readHash_refuses_a_short_digest` |
| a `yesterday` priority | `Fin 8`, through the one reader of a stored `p` | `Planner.mkYesterday?` | `readYesterday_refuses_a_priority_past_seven` |
| the `yesterday` list | `Planner.maxCands` | `Planner.mkYesterday?` | `readYesterday_refuses_past_the_cap` |
| a routine's `durMin`, an override's minutes | `CapWire.maxRemaining` (fork `u32`) | `EmitWire.u32Within` | `readRoutine_refuses_a_duration_past_the_width`, `readOverrides_refuses_an_estimate_past_the_width` |
| the override lists | `Planner.maxCands` | `Planner.mkOverrides?` | `readOverrides_refuses_too_many_estimates`, `readOverrides_refuses_too_many_drops` |
| `prio.batchMaxMin` | `CapWire.maxRemaining` (fork `u32`) | `EmitWire.u32Within` | `readBatchMaxMin_refuses_past_the_width` |
| the routine list, and each instance's rule | `Planner.maxCands`, `Planner.mkRoutine?` | `Planner.mkRoutines?` | already proved — `mkRoutines?_refuses_too_many`, and `PlannerWit.mkPlanReq?_refuses_a_routine_the_rule_refuses` carries it out |

**`batchMaxMin` takes the fork's `u32` and not the day's 1,440.**  `config.rs:361` declares
`pub batch_max_min: u32`; a tighter bound here would be a *divergence from the comparand*
(D21/D22/D23) and would owe a parity number, where the `u32` width is the value the fork can
actually hold.  `EmitWire.u32Within` is the guard and `CapWire.maxRemaining` is
`Look.maxPlanMinutes` is that width — one function, one number, no third name.

## §10.3's family, and the two names that are deliberately NOT declared

Design §10.3 reserves `planRefusal.*` for `badState`, badWindow, badBudget, `badActive`,
`badBreak`, `badInterrupt`, `badHash`, `badOverride` and tooManyCands — the three spelled
without backticks because nothing declares them and check 8 is right to ask.

**The type is `PlannerRefusal` and deliberately NOT PlanRefusal.**  Four ledger sentences and
`Planner.dayPlan`'s own header cite PlanRefusal as a type that **does not exist**, because
`dayPlan` is total (D28) and has no error type — `kernel/citations-allow.txt` carries the name
under *"names D28 says do NOT exist"* with five counted citations.  Declaring a type of that
name here would make five committed sentences false while `dayPlan`'s signature was unchanged,
which is a ledger rot the checks would not catch: check 8 would go **quieter**, not louder, as
the allow entry stopped being needed.  So the wire key is `planner`, the type is
`PlannerRefusal`, and PlanRefusal still does not exist.

Seven of §10.3's nine names are below.  **badWindow and badBudget are not, and their absence is
the point**:
`Planner.PlanReq` has no window field and no budget field — `PlanReq.window` is
`Look.day0Window r.look` and `PlanReq.budgetBlocks` is the stored one or `Look.budgetOf`, both
*views*, and `PlanReq.window_is_the_lookaheads` is the theorem that says so.  There is nothing
on this wire for either name to be about, so declaring them would put two constructors in
`PlannerRefusal` that **no input can reach** — AGENTS §9.2's disguised gap, in the one place R10
is supposed to prevent it.  tooManyCands is likewise absent: the candidate cap is
`capacity.candidates`', refused there as `Boundary.Refusal.tooManyCandidates` before this
section is read at all.  README gap **1664**.

**`EmitWire.RowRefusal` is deliberately not this family** and this module does not rename it:
the two live in one `plan` object with disjoint keys, exactly as `EmitWire.lean`'s header says
R3 would arrange them, and `Planner.dayPlan` stays **total** (D28) — nothing here makes it an
`Except`, and a refusal in this module is a refusal to *build the request*, never a refusal by
the planner.

## Reusing `EmitWire`'s readers rather than writing them again

`EmitWire.asPlan` and the eight readers over it (`natAtP`, `strAtP`, `arrAtP`, `optAtP`,
`flagAtP`, `optNatAtP`, `optStrAtP`) and the three guards (`idWithin`, `u32Within`,
`secWithin`) were typed to `RowRefusal`.  They are now **polymorphic in the refusal**
(`{ρ : Type}`), which is the smallest edit that lets this section reuse them by name instead of
copying nine JSON shapes and three bounds one module along.  Every existing call site and every
existing theorem is unchanged in meaning: `ρ` unifies with `RowRefusal` exactly where it did
before, and `asPlan_keeps_the_value` / `asPlan_renames_a_refusal` are now *stronger*
statements (∀ ρ) that imply the ones they replace (D5).
-/

namespace Tm
namespace PlanWire

open Planner (RuntimeIn RoutineIn PlanOverrides ActiveBlock BreakState BreakPlace
  InterruptState PlanHash PrioCfg Capped)

/-! ## The section's names (AGENTS §5.7: every diagnostic is named) -/

/-- A key of the `planner` section, or of one of its records. -/
inductive PlanKey
  | state | active | brk | interrupt | lastHash | yesterday
  | routines | overrides | batchMaxMin
  | id | inst | started | estMin | paused | plannedMin | place
  | winLo | winHi | durMin | mandatory
  | est | extra | drop | min
  /-- **The record's own well-formedness**, when `Planner.mkActive?`, `mkBreak?` or
  `mkInterrupt?` answers `none`.  Those three answer `Option` and not a named error, so the wire
  can say *which record* the planner could not hold and not *which clause* of its `wf` failed —
  README gap **1665**, and the reason this key is not one of the field names above. -/
  | wf
deriving DecidableEq, Repr

def PlanKey.name : PlanKey → String
  | .state => "state" | .active => "active" | .brk => "break"
  | .interrupt => "interrupt" | .lastHash => "lastHash" | .yesterday => "yesterday"
  | .routines => "routines" | .overrides => "overrides" | .batchMaxMin => "batchMaxMin"
  | .id => "id" | .inst => "inst" | .started => "started" | .estMin => "estMin"
  | .paused => "paused" | .plannedMin => "plannedMin" | .place => "place"
  | .winLo => "winLo" | .winHi => "winHi" | .durMin => "durMin"
  | .mandatory => "mandatory" | .est => "est" | .extra => "extra"
  | .drop => "drop" | .min => "min" | .wf => "wf"

/-- **The planner section's refusals** (design §10.3's `planRefusal.*`).  Each names the record
it is about by position where there is a position, and the key by name, exactly as
`EmitWire.RowRefusal` does for the rows. -/
inductive PlannerRefusal
  /-- The section is not an object, or a key is carried twice. -/
  | shape
  /-- A key of the `state` object itself. -/
  | badState (k : PlanKey)
  /-- A key of `state.active`. -/
  | badActive (k : PlanKey)
  /-- A key of `state.break`. -/
  | badBreak (k : PlanKey)
  /-- A key of `state.interrupt`. -/
  | badInterrupt (k : PlanKey)
  /-- `state.lastHash` is not `hashHexLen` hex digits. -/
  | badHash
  /-- The `yesterday` record at this position. -/
  | badYesterday (i : Nat)
  /-- More stored priorities than the candidate cap, or a `p` past seven. -/
  | badYesterdayList
  /-- A key of the routine record at this position. -/
  | badRoutine (i : Nat) (k : PlanKey)
  /-- A key of the `overrides` object, or of one of its records. -/
  | badOverride (k : PlanKey)
  /-- More overrides than the candidate cap. -/
  | tooManyOverrides
  /-- §16's `[priority] batch_max_min` is absent or past the fork's `u32`. -/
  | badBatchMaxMin
  /-- The section needs the `capacity` section: `PlanReq.look` is `Look.mkInput?`'s answer for
  it and `prio`'s five values are its `priority` object's, so a planner request without one
  could not be assembled whatever else it carried. -/
  | capacityAbsent
deriving DecidableEq, Repr

def PlannerRefusal.text : PlannerRefusal → String
  | .shape => "shape"
  | .badState k => s!"badState {k.name}"
  | .badActive k => s!"badActive {k.name}"
  | .badBreak k => s!"badBreak {k.name}"
  | .badInterrupt k => s!"badInterrupt {k.name}"
  | .badHash => "badHash"
  | .badYesterday i => s!"badYesterday {i}"
  | .badYesterdayList => "badYesterdayList"
  | .badRoutine i k => s!"badRoutine {i} {k.name}"
  | .badOverride k => s!"badOverride {k.name}"
  | .tooManyOverrides => "tooManyOverrides"
  | .badBatchMaxMin => "badBatchMaxMin"
  | .capacityAbsent => "capacityAbsent"

/-- The refusal on the wire: `{"err": {"planner": "<name> <key>"}}` — `EmitWire`'s shape under
this section's own key, so a host tells the two families apart by the key and not by the text. -/
def plannerRefusalJson (r : PlannerRefusal) : JVal :=
  jone "err" (jone "planner" (.str r.text.toList))

/-! ## The one guard this module adds, and the theorem that says it is not a bound

`EmitWire.secWithin` already reads an absolute second through `Cal.mkInstant?`.  Three fields
here want the `Cal.Instant` rather than the `Nat`, and `instantWithin` is that and **nothing
else**: `instantWithin_is_secWithin_at_the_zero_nanosecond` is the sentence as a theorem, in
the shape `EmitWire.secWithin_is_the_clause_Seg_wf_puts_on_a_stop` established. -/

/-- An absolute second as the instant the planner's records hold. -/
def instantWithin {ρ : Type} (r : ρ) (sec : Nat) : Except ρ Cal.Instant :=
  (EmitWire.secWithin r sec).map (fun s => ⟨s, 0⟩)

/-- **It is `secWithin`, at the zero nanosecond** — not a second bound. -/
theorem instantWithin_is_secWithin_at_the_zero_nanosecond {ρ : Type} (r : ρ) (sec : Nat) :
    instantWithin r sec = (EmitWire.secWithin r sec).map (fun s => ⟨s, 0⟩) := rfl

/-- **A second past the calendar is refused**, through the constructor and not through a
comparison written here. -/
theorem instantWithin_refuses_past_the_calendar {ρ : Type} (r : ρ) (sec : Nat)
    (h : Cal.mkInstant? sec 0 = none) : instantWithin r sec = .error r := by
  unfold instantWithin EmitWire.secWithin
  rw [h]; rfl

/-- And a representable second is accepted, and comes back unchanged (AGENTS §5.8). -/
theorem instantWithin_accepts_a_representable_second {ρ : Type} (r : ρ) (sec : Nat)
    (i : Cal.VInstant) (h : Cal.mkInstant? sec 0 = some i) :
    instantWithin r sec = .ok ⟨i.val.sec, 0⟩ := by
  unfold instantWithin EmitWire.secWithin
  rw [h]; rfl

/-- **Both ends are inhabited**: 315,537,897,600 is the first second outside chrono's years and
315,537,897,599 is inside, so neither theorem above is vacuous. -/
theorem instantWithin_refuses_the_first_second_past_the_years {ρ : Type} (r : ρ) :
    instantWithin r 315537897600 = .error r
      ∧ instantWithin r 315537897599 = .ok ⟨315537897599, 0⟩ := by
  constructor <;> rfl

/-! ## `state` — §9's five rows `Look.Today` does not carry -/

/-- `state.active`, through `Planner.mkActive?` — the one constructor that knows what a running
block may be.  `paused` is absent-is-`false`, which is the field's own default. -/
def readActive (now : Cal.Instant) (v : JVal) : Except PlannerRefusal ActiveBlock := do
  let idS ← EmitWire.strAtP v "id" (PlannerRefusal.badActive PlanKey.id)
  let id ← EmitWire.idWithin (PlannerRefusal.badActive PlanKey.id) idS
  let secN ← EmitWire.natAtP v "started" (PlannerRefusal.badActive PlanKey.started)
  let started ← instantWithin (PlannerRefusal.badActive PlanKey.started) secN
  let estMin ← EmitWire.natAtP v "estMin" (PlannerRefusal.badActive PlanKey.estMin)
  let paused ← EmitWire.flagAtP v "paused" (PlannerRefusal.badActive PlanKey.paused)
  match Planner.mkActive? now ⟨id, started, estMin, paused⟩ with
  | some a => pure a.val
  | none => throw (PlannerRefusal.badActive PlanKey.wf)

/-- An absent or `null` `active` is nothing running. -/
def readOptActive (now : Cal.Instant) (v : JVal) : Except PlannerRefusal (Option ActiveBlock) :=
  match EmitWire.optAtP v "active" (PlannerRefusal.badState PlanKey.active) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some w) => (readActive now w).map some

/-- Fork `store::BreakPlace`'s four serde names.  An unknown word is refused by name, never
defaulted (AGENTS §5.7). -/
def placeOf? (s : List Char) : Option BreakPlace :=
  if s = "walk".toList then some .walk
  else if s = "seat".toList then some .seat
  else if s = "bed".toList then some .bed
  else if s = "phone".toList then some .phone
  else none

/-- `state.break`, through `Planner.mkBreak?`. -/
def readBreak (now : Cal.Instant) (v : JVal) : Except PlannerRefusal BreakState := do
  let secO ← EmitWire.optNatAtP v "started" (PlannerRefusal.badBreak PlanKey.started)
  let started ← match secO with
    | none => pure none
    | some n => (instantWithin (PlannerRefusal.badBreak PlanKey.started) n).map some
  let plannedMin ← EmitWire.natAtP v "plannedMin" (PlannerRefusal.badBreak PlanKey.plannedMin)
  let placeS ← EmitWire.optStrAtP v "place" (PlannerRefusal.badBreak PlanKey.place)
  let place ← match placeS with
    | none => pure none
    | some w => match placeOf? w with
      | some p => pure (some p)
      | none => throw (PlannerRefusal.badBreak PlanKey.place)
  match Planner.mkBreak? now ⟨started, plannedMin, place⟩ with
  | some b => pure b.val
  | none => throw (PlannerRefusal.badBreak PlanKey.wf)

def readOptBreak (now : Cal.Instant) (v : JVal) : Except PlannerRefusal (Option BreakState) :=
  match EmitWire.optAtP v "break" (PlannerRefusal.badState PlanKey.brk) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some w) => (readBreak now w).map some

/-- `state.interrupt`, through `Planner.mkInterrupt?`.  §9's open interruption is an ad-hoc wall
from `t_i` to `now` and both of its fields are optional. -/
def readInterrupt (now : Cal.Instant) (v : JVal) : Except PlannerRefusal InterruptState := do
  let secO ← EmitWire.optNatAtP v "started" (PlannerRefusal.badInterrupt PlanKey.started)
  let started ← match secO with
    | none => pure none
    | some n => (instantWithin (PlannerRefusal.badInterrupt PlanKey.started) n).map some
  let idO ← EmitWire.optStrAtP v "id" (PlannerRefusal.badInterrupt PlanKey.id)
  let id ← match idO with
    | none => pure none
    | some s => (EmitWire.idWithin (PlannerRefusal.badInterrupt PlanKey.id) s).map some
  match Planner.mkInterrupt? now ⟨started, id⟩ with
  | some x => pure x.val
  | none => throw (PlannerRefusal.badInterrupt PlanKey.wf)

def readOptInterrupt (now : Cal.Instant) (v : JVal) :
    Except PlannerRefusal (Option InterruptState) :=
  match EmitWire.optAtP v "interrupt" (PlannerRefusal.badState PlanKey.interrupt) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some w) => (readInterrupt now w).map some

/-- `state.lastHash`, through `Planner.mkHash?` — the one hex reader (R10). -/
def readHash (v : JVal) : Except PlannerRefusal (Option PlanHash) :=
  match EmitWire.optStrAtP v "lastHash" (PlannerRefusal.badState PlanKey.lastHash) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some s) => match Planner.mkHash? s with
    | some h => .ok (some h)
    | none => .error PlannerRefusal.badHash

/-- One `{"id": …, "p": …}` pair of `state.yesterday`, the id bounded and the `p` left to
`mkYesterday?` — the one reader of a stored priority. -/
def readYesterdayPair (i : Nat) (v : JVal) : Except PlannerRefusal (Id × Nat) := do
  let idS ← EmitWire.strAtP v "id" (PlannerRefusal.badYesterday i)
  let id ← EmitWire.idWithin (PlannerRefusal.badYesterday i) idS
  let p ← EmitWire.natAtP v "p" (PlannerRefusal.badYesterday i)
  pure (id, p)

/-- `state.priorities_yesterday` (§7.4), the cap and the `Fin 8` both through
`Planner.mkYesterday?`.  Nothing here restates either. -/
def readYesterday (xs : List JVal) : Except PlannerRefusal (Capped (Id × Fin 8)) :=
  match xs.zipIdx.mapM (fun p => readYesterdayPair p.2 p.1) with
  | .error e => .error e
  | .ok ps => match Planner.mkYesterday? ps with
    | some c => .ok c
    | none => .error PlannerRefusal.badYesterdayList

/-- **§9's five rows.**  Every one is optional and every absence is the field's own empty. -/
def readState (now : Cal.Instant) (sec : JVal) : Except PlannerRefusal RuntimeIn := do
  let active ← readOptActive now sec
  let brk ← readOptBreak now sec
  let interrupt ← readOptInterrupt now sec
  let lastHash ← readHash sec
  let ys ← match ← EmitWire.optAtP sec "yesterday" (PlannerRefusal.badState PlanKey.yesterday) with
    | none => pure []
    | some (.arr xs) => pure xs
    | some _ => throw (PlannerRefusal.badState PlanKey.yesterday)
  let yesterday ← readYesterday ys
  pure ⟨active, brk, interrupt, lastHash, yesterday⟩

/-! ## `routines` — §8.2 step 2's window instances, host-collected until F2 (K3) -/

/-- One `RoutineIn`.  The cap and the per-instance rule are `Planner.mkRoutines?`' and are not
restated here (AGENTS §5.3); this reader owns the field shapes and their widths alone. -/
def readRoutine (i : Nat) (v : JVal) : Except PlannerRefusal RoutineIn := do
  let idS ← EmitWire.strAtP v "id" (PlannerRefusal.badRoutine i PlanKey.id)
  let id ← EmitWire.idWithin (PlannerRefusal.badRoutine i PlanKey.id) idS
  let instO ← EmitWire.optStrAtP v "inst" (PlannerRefusal.badRoutine i PlanKey.inst)
  let inst ← match instO with
    | none => pure none
    | some s => (EmitWire.idWithin (PlannerRefusal.badRoutine i PlanKey.inst) s).map some
  let loN ← EmitWire.natAtP v "winLo" (PlannerRefusal.badRoutine i PlanKey.winLo)
  let lo ← EmitWire.secWithin (PlannerRefusal.badRoutine i PlanKey.winLo) loN
  let hiN ← EmitWire.natAtP v "winHi" (PlannerRefusal.badRoutine i PlanKey.winHi)
  let hi ← EmitWire.secWithin (PlannerRefusal.badRoutine i PlanKey.winHi) hiN
  let durN ← EmitWire.natAtP v "durMin" (PlannerRefusal.badRoutine i PlanKey.durMin)
  let dur ← EmitWire.u32Within (PlannerRefusal.badRoutine i PlanKey.durMin) durN
  let mandatory ← EmitWire.flagAtP v "mandatory" (PlannerRefusal.badRoutine i PlanKey.mandatory)
  pure ⟨id, inst, lo, hi, dur, mandatory⟩

/-- The instances, read at their positions.  **Uncapped here on purpose**: `mkRoutines?` refuses
a list past `Planner.maxCands` *before* its map runs, and a cap written here as well would be
the second statement of one bound. -/
def readRoutines (xs : List JVal) : Except PlannerRefusal (List RoutineIn) :=
  xs.zipIdx.mapM (fun p => readRoutine p.2 p.1)

/-! ## `overrides` — §9.1's what-if inputs, alive for one call -/

/-- One `{"id": …, "min": …}` record of `est` or `extra`. -/
def readOverridePair (k : PlanKey) (v : JVal) : Except PlannerRefusal (Id × Nat) := do
  let idS ← EmitWire.strAtP v "id" (PlannerRefusal.badOverride k)
  let id ← EmitWire.idWithin (PlannerRefusal.badOverride k) idS
  let mN ← EmitWire.natAtP v "min" (PlannerRefusal.badOverride k)
  let m ← EmitWire.u32Within (PlannerRefusal.badOverride k) mN
  pure (id, m)

/-- An array at `k`, absent being empty. -/
def readOverrideList (v : JVal) (key : String) (k : PlanKey) : Except PlannerRefusal (List JVal) :=
  match EmitWire.optAtP v key (PlannerRefusal.badOverride k) with
  | .error e => .error e
  | .ok none => .ok []
  | .ok (some (.arr xs)) => .ok xs
  | .ok (some _) => .error (PlannerRefusal.badOverride k)

/-- The `drop` list: ids and nothing else, each through `EmitWire.idWithin`.  A name of its
own, so the two cap theorems below can quantify over its answer without restating its body. -/
def readDropIds (xs : List JVal) : Except PlannerRefusal (List Id) :=
  xs.mapM (fun w => match w with
    | .str s => EmitWire.idWithin (PlannerRefusal.badOverride PlanKey.drop) s
    | _ => throw (PlannerRefusal.badOverride PlanKey.drop))

/-- The three lists, each capped by `Planner.mkOverrides?` and not by a guard written here. -/
def readOverrides (v : JVal) : Except PlannerRefusal PlanOverrides := do
  let estJ ← readOverrideList v "est" PlanKey.est
  let est ← estJ.mapM (readOverridePair PlanKey.est)
  let extraJ ← readOverrideList v "extra" PlanKey.extra
  let extra ← extraJ.mapM (readOverridePair PlanKey.extra)
  let dropJ ← readOverrideList v "drop" PlanKey.drop
  let drop ← readDropIds dropJ
  match Planner.mkOverrides? est extra drop with
  | some o => pure o
  | none => throw PlannerRefusal.tooManyOverrides

/-- An absent or `null` `overrides` is no what-if. -/
def readOptOverrides (sec : JVal) : Except PlannerRefusal (Option PlanOverrides) :=
  match EmitWire.optAtP sec "overrides" (PlannerRefusal.badOverride PlanKey.est) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some w) => (readOverrides w).map some

/-! ## `prio.batchMaxMin` — README gap 801, discharged

§16 puts `batch_max_min` in the `[priority]` table beside the bin ladder, the safety factor and
`default_priority`, and `Boundary.CapWire.readPriority` already reads those three off
`capacity.priority` with no default and a named refusal each.  This reads the fourth key of the
same object — **one key, one reader** — rather than opening a second home for a §16 value. -/

/-- §16's `[priority] batch_max_min`, off the capacity section's own `priority` object.  Absent
is refused by name: `readPriority` defaults none of its three either, and a default written here
would be a second copy of `config.rs:371`'s 20. -/
def readBatchMaxMin (cap : JVal) : Except PlannerRefusal Nat :=
  match EmitWire.optAtP cap "priority" PlannerRefusal.badBatchMaxMin with
  | .error e => .error e
  | .ok none => .error PlannerRefusal.badBatchMaxMin
  | .ok (some pv) =>
    match EmitWire.natAtP pv "batchMaxMin" PlannerRefusal.badBatchMaxMin with
    | .error e => .error e
    | .ok n => EmitWire.u32Within PlannerRefusal.badBatchMaxMin n

/-! ## The section, decoded -/

/-- **The `planner` section's three values.**  `prio` is *not* here: its first four fields are
the capacity section's and its fifth is `readBatchMaxMin`'s, so this record carries what the
section itself owns and nothing it would be a second reader of. -/
structure PlannerIn where
  state     : RuntimeIn
  routines  : List RoutineIn
  overrides : Option PlanOverrides

/-- The section: `state`, `routines`, `overrides`.  All three are optional and each absence is
the value's own empty — a host that plans with nothing running, no window instance due and no
what-if sends `{}`. -/
def readPlannerSection (now : Cal.Instant) (sec : JVal) : Except PlannerRefusal PlannerIn := do
  let st ← match ← EmitWire.optAtP sec "state" (PlannerRefusal.badState PlanKey.state) with
    | none => pure RuntimeIn.empty
    | some w => readState now w
  let rs ← match ← EmitWire.optAtP sec "routines" (PlannerRefusal.badRoutine 0 PlanKey.routines) with
    | none => pure []
    | some (.arr xs) => readRoutines xs
    | some _ => throw (PlannerRefusal.badRoutine 0 PlanKey.routines)
  let ov ← readOptOverrides sec
  pure ⟨st, rs, ov⟩

/-! ## The laws

### The names spell themselves -/

/-- **The section's keys spell themselves**, so a key renamed here moves a refusal's text and
the test that reads it fails, rather than the wire quietly changing. -/
theorem planKey_names_are_the_wire_keys :
    (PlanKey.state.name, PlanKey.active.name, PlanKey.brk.name, PlanKey.interrupt.name,
     PlanKey.lastHash.name, PlanKey.yesterday.name, PlanKey.routines.name,
     PlanKey.overrides.name, PlanKey.batchMaxMin.name)
      = ("state", "active", "break", "interrupt", "lastHash", "yesterday", "routines",
         "overrides", "batchMaxMin") := rfl

/-- And the record keys. -/
theorem planKey_record_names_are_the_wire_keys :
    (PlanKey.id.name, PlanKey.inst.name, PlanKey.started.name, PlanKey.estMin.name,
     PlanKey.paused.name, PlanKey.plannedMin.name, PlanKey.place.name, PlanKey.winLo.name,
     PlanKey.winHi.name, PlanKey.durMin.name, PlanKey.mandatory.name, PlanKey.est.name,
     PlanKey.extra.name, PlanKey.drop.name, PlanKey.min.name)
      = ("id", "inst", "started", "estMin", "paused", "plannedMin", "place", "winLo",
         "winHi", "durMin", "mandatory", "est", "extra", "drop", "min") := rfl

/-- **Every refusal spells itself, with its position and its key** — the sentence a host reads
when the request is refused. -/
theorem the_refusals_spell_themselves :
    (PlannerRefusal.shape.text, (PlannerRefusal.badState PlanKey.active).text,
     (PlannerRefusal.badActive PlanKey.id).text, (PlannerRefusal.badBreak PlanKey.place).text,
     (PlannerRefusal.badInterrupt PlanKey.wf).text, PlannerRefusal.badHash.text,
     (PlannerRefusal.badYesterday 3).text, PlannerRefusal.badYesterdayList.text,
     (PlannerRefusal.badRoutine 2 PlanKey.winLo).text,
     (PlannerRefusal.badOverride PlanKey.drop).text, PlannerRefusal.tooManyOverrides.text,
     PlannerRefusal.badBatchMaxMin.text, PlannerRefusal.capacityAbsent.text)
      = ("shape", "badState active", "badActive id", "badBreak place",
         "badInterrupt wf", "badHash", "badYesterday 3", "badYesterdayList",
         "badRoutine 2 winLo", "badOverride drop", "tooManyOverrides",
         "badBatchMaxMin", "capacityAbsent") := rfl

/-- **And the shape it goes out in**: `{"err":{"planner":"<name> <key>"}}`, beside — and not
inside — `EmitWire`'s `{"err":{"plan":…}}`.  A host that sees `planner` knows the request could
not be *built*; a host that sees `plan` knows a row could not be *read*. -/
theorem plannerRefusalJson_is_the_err_planner_shape :
    plannerRefusalJson PlannerRefusal.badHash
      = jone "err" (jone "planner" (.str "badHash".toList)) := rfl

/-- **The two families' wire keys are different words**, which is what lets one `plan` object
carry both R3's keys and W-24's without a reader having to guess. -/
theorem the_two_refusal_families_do_not_share_a_key :
    plannerRefusalJson PlannerRefusal.shape ≠ EmitWire.rowRefusalJson EmitWire.RowRefusal.shape := by
  decide

/-! ### `state`'s rejection theorems (R10) -/

/-- **An `active.id` past `CapWire.maxCandId` is refused**, through `EmitWire.idWithin` — the
one guard, not a comparison written here. -/
theorem readActive_refuses_a_long_id (now : Cal.Instant) (v : JVal) (id : Id)
    (hs : EmitWire.strAtP v "id" (PlannerRefusal.badActive PlanKey.id) = .ok id)
    (h : CapWire.maxCandId < id.length) :
    readActive now v = .error (PlannerRefusal.badActive PlanKey.id) := by
  simp only [readActive, hs, bind, Except.bind,
    EmitWire.idWithin_refuses_a_long_id (PlannerRefusal.badActive PlanKey.id) id h]

/-- **An `active.started` past the calendar is refused**, through `Cal.mkInstant?`. -/
theorem readActive_refuses_a_start_past_the_calendar (now : Cal.Instant) (v : JVal) (id : Id)
    (n : Nat) (hs : EmitWire.strAtP v "id" (PlannerRefusal.badActive PlanKey.id) = .ok id)
    (hlen : id.length ≤ CapWire.maxCandId)
    (hn : EmitWire.natAtP v "started" (PlannerRefusal.badActive PlanKey.started) = .ok n)
    (h : Cal.mkInstant? n 0 = none) :
    readActive now v = .error (PlannerRefusal.badActive PlanKey.started) := by
  simp only [readActive, hs, hn, bind, Except.bind,
    EmitWire.idWithin_accepts_at_the_bound (PlannerRefusal.badActive PlanKey.id) id hlen,
    instantWithin_refuses_past_the_calendar (PlannerRefusal.badActive PlanKey.started) n h]

/-- **A running block that started after `now` is refused**, through `Planner.mkActive?` — the
constructor whose `wf` says what a running block may be. -/
theorem readActive_refuses_a_start_after_now (now : Cal.Instant) (v : JVal) (id : Id)
    (n est : Nat) (paused : Bool) (i : Cal.VInstant)
    (hs : EmitWire.strAtP v "id" (PlannerRefusal.badActive PlanKey.id) = .ok id)
    (hlen : id.length ≤ CapWire.maxCandId)
    (hn : EmitWire.natAtP v "started" (PlannerRefusal.badActive PlanKey.started) = .ok n)
    (hi : Cal.mkInstant? n 0 = some i)
    (he : EmitWire.natAtP v "estMin" (PlannerRefusal.badActive PlanKey.estMin) = .ok est)
    (hp : EmitWire.flagAtP v "paused" (PlannerRefusal.badActive PlanKey.paused) = .ok paused)
    (h : now.sec < i.val.sec) :
    readActive now v = .error (PlannerRefusal.badActive PlanKey.wf) := by
  simp only [readActive, hs, hn, he, hp, bind, Except.bind,
    EmitWire.idWithin_accepts_at_the_bound (PlannerRefusal.badActive PlanKey.id) id hlen,
    instantWithin_accepts_a_representable_second (PlannerRefusal.badActive PlanKey.started) n i hi,
    Planner.mkActive?_refuses_a_start_after_now now ⟨id, ⟨i.val.sec, 0⟩, est, paused⟩ h]
  rfl

/-- **An `estMin` past the day is refused**, through the same constructor — `Look.maxDayMin` is
the day's own bound and this module does not write a second one. -/
theorem readActive_refuses_an_estimate_past_the_day (now : Cal.Instant) (v : JVal) (id : Id)
    (n est : Nat) (paused : Bool) (i : Cal.VInstant)
    (hs : EmitWire.strAtP v "id" (PlannerRefusal.badActive PlanKey.id) = .ok id)
    (hlen : id.length ≤ CapWire.maxCandId)
    (hn : EmitWire.natAtP v "started" (PlannerRefusal.badActive PlanKey.started) = .ok n)
    (hi : Cal.mkInstant? n 0 = some i)
    (he : EmitWire.natAtP v "estMin" (PlannerRefusal.badActive PlanKey.estMin) = .ok est)
    (hp : EmitWire.flagAtP v "paused" (PlannerRefusal.badActive PlanKey.paused) = .ok paused)
    (h : Look.maxDayMin < est) :
    readActive now v = .error (PlannerRefusal.badActive PlanKey.wf) := by
  simp only [readActive, hs, hn, he, hp, bind, Except.bind,
    EmitWire.idWithin_accepts_at_the_bound (PlannerRefusal.badActive PlanKey.id) id hlen,
    instantWithin_accepts_a_representable_second (PlannerRefusal.badActive PlanKey.started) n i hi,
    Planner.mkActive?_refuses_an_estimate_past_the_day now ⟨id, ⟨i.val.sec, 0⟩, est, paused⟩ h]
  rfl

/-- And a real running block reads, so none of the three refusals above is the only outcome
(AGENTS §5.8), and the fields land where they say they do. -/
theorem readActive_accepts_a_running_block :
    readActive ⟨1000, 0⟩ (.obj [("id".toList, .str "m2".toList),
      ("started".toList, .num 900), ("estMin".toList, .num 60)])
      = .ok ⟨"m2".toList, ⟨900, 0⟩, 60, false⟩ := by rfl

/-- **A `break` longer than a day is refused**, through `Planner.mkBreak?`. -/
theorem readBreak_refuses_a_break_longer_than_a_day :
    readBreak ⟨1000, 0⟩ (.obj [("plannedMin".toList, .num 1441)])
      = .error (PlannerRefusal.badBreak PlanKey.wf) := by rfl

/-- **An unknown `place` word is refused by name**, never defaulted to a seat. -/
theorem readBreak_refuses_an_unknown_place :
    readBreak ⟨1000, 0⟩ (.obj [("plannedMin".toList, .num 10),
      ("place".toList, .str "hammock".toList)])
      = .error (PlannerRefusal.badBreak PlanKey.place) := by rfl

/-- And the four words read, so `placeOf?` is a reader and not a refusal.

**Named without the `?`** on purpose: `mutate.py` records a pin site as a bare line number plus
the declaration name it parsed there, and its parser stops at the `?` — the roster came back
saying *"roster says PlanWire.lean:581 placeOf, PlanWire.lean:581 is now in
placeOf?_reads_the_four"* — the name this theorem carried until the rename, spelled without
backticks because nothing declares it and check 8 is right to ask — and check 9 FAILED on a
drift that was not one.  Every
`mk…?_refuses_…` theorem in `Planner.lean` is the same shape and would hit it the day one of
them became a recorded pin site.  README gap **1666**. -/
theorem the_four_break_places_read :
    (placeOf? "walk".toList, placeOf? "seat".toList, placeOf? "bed".toList,
     placeOf? "phone".toList)
      = (some BreakPlace.walk, some BreakPlace.seat, some BreakPlace.bed,
         some BreakPlace.phone) := by decide

/-- **A break that started after `now` is refused**, through `Planner.mkBreak?` — the other
clause of the same `wf`, under the same name for the reason `PlanKey.wf` records. -/
theorem readBreak_refuses_a_start_after_now :
    readBreak ⟨1000, 0⟩ (.obj [("started".toList, .num 1001),
      ("plannedMin".toList, .num 10)])
      = .error (PlannerRefusal.badBreak PlanKey.wf) := by rfl

/-- A real break reads. -/
theorem readBreak_accepts_a_running_break :
    readBreak ⟨1000, 0⟩ (.obj [("started".toList, .num 900),
      ("plannedMin".toList, .num 10), ("place".toList, .str "walk".toList)])
      = .ok ⟨some ⟨900, 0⟩, 10, some BreakPlace.walk⟩ := by rfl

/-- **An interruption that started after `now` is refused**, through `Planner.mkInterrupt?`. -/
theorem readInterrupt_refuses_a_start_after_now :
    readInterrupt ⟨1000, 0⟩ (.obj [("started".toList, .num 1001)])
      = .error (PlannerRefusal.badInterrupt PlanKey.wf) := by rfl

/-- **An interruption's `id` past the bound is refused**, through `EmitWire.idWithin`. -/
theorem readInterrupt_refuses_a_long_id (now : Cal.Instant) (v : JVal) (id : Id)
    (hs : EmitWire.optNatAtP v "started" (PlannerRefusal.badInterrupt PlanKey.started) = .ok none)
    (hi : EmitWire.optStrAtP v "id" (PlannerRefusal.badInterrupt PlanKey.id) = .ok (some id))
    (h : CapWire.maxCandId < id.length) :
    readInterrupt now v = .error (PlannerRefusal.badInterrupt PlanKey.id) := by
  simp only [readInterrupt, hs, hi, bind, Except.bind, Except.map,
    EmitWire.idWithin_refuses_a_long_id (PlannerRefusal.badInterrupt PlanKey.id) id h]
  rfl

/-- A real interruption reads. -/
theorem readInterrupt_accepts_an_open_interruption :
    readInterrupt ⟨1000, 0⟩ (.obj [("started".toList, .num 900),
      ("id".toList, .str "m1".toList)])
      = .ok ⟨some ⟨900, 0⟩, some "m1".toList⟩ := by rfl

/-- **A `lastHash` that is not `hashHexLen` hex digits is refused**, through `Planner.mkHash?` —
the kernel's one hex reader. -/
theorem readHash_refuses_a_short_digest (v : JVal) (s : List Char)
    (hs : EmitWire.optStrAtP v "lastHash" (PlannerRefusal.badState PlanKey.lastHash)
      = .ok (some s)) (h : s.length ≠ Planner.hashHexLen) :
    readHash v = .error PlannerRefusal.badHash := by
  simp only [readHash, hs, Planner.mkHash?_refuses_a_short_digest s h]

/-- And sixteen hex digits read, so the refusal is not the only outcome. -/
theorem readHash_accepts_sixteen_hex_digits :
    (readHash (.obj [("lastHash".toList, .str "00000000000000ff".toList)])).map
        (fun o => o.map (fun h => h.val)) = .ok (some 255) := by rfl

/-- **An absent `lastHash` is no hash**, which is the field's own `none` and not a zero. -/
theorem readHash_of_an_absent_hash : readHash (.obj []) = .ok none := rfl

/-- **A stored `p` past seven is refused**, through `Planner.mkYesterday?` — the one reader. -/
theorem readYesterday_refuses_a_priority_past_seven :
    readYesterday [.obj [("id".toList, .str "m1".toList), ("p".toList, .num 8)]]
      = .error PlannerRefusal.badYesterdayList := by rfl

/-- And seven reads, so the refusal is not the only outcome. -/
theorem readYesterday_accepts_seven :
    (readYesterday [.obj [("id".toList, .str "m1".toList), ("p".toList, .num 7)]]).map
        (fun c => c.val.map (fun p => (p.1, p.2.val))) = .ok [("m1".toList, 7)] := by rfl

/-- **More stored priorities than the candidate cap is refused**, through the same constructor
— `Planner.maxCands`, not a number written here. -/
theorem readYesterday_refuses_past_the_cap (xs : List JVal) (ps : List (Id × Nat))
    (hp : xs.zipIdx.mapM (fun p => readYesterdayPair p.2 p.1) = .ok ps)
    (h : Planner.maxCands < ps.length) :
    readYesterday xs = .error PlannerRefusal.badYesterdayList := by
  simp only [readYesterday, hp, Planner.mkYesterday?_refuses_too_many ps h]

/-- The empty list reads, so the two refusals above are not vacuous. -/
theorem readYesterday_of_nil : (readYesterday []).map (fun c => c.val) = .ok [] := rfl

/-- **The empty `state` object is `RuntimeIn.empty`** — every field's own absence, and not a
defaulted value picked by the reader (AGENTS §5.6). -/
theorem readState_of_an_empty_object (now : Cal.Instant) :
    readState now (.obj []) = .ok RuntimeIn.empty := rfl

/-- **A day with everything running reads.**  This theorem exists because `mutate.py` said it
had to: `readState_of_an_empty_object` above is satisfied by a reader that answers `none`
whatever it is given, and the three optional readers all came back **SURVIVED** at `:= default`
until a request with `active`, `break`, `interrupt`, `lastHash` and `yesterday` all present was
written down.  An absence proves an optional reader nothing (AGENTS §9.2). -/
theorem readState_accepts_a_running_day :
    (readState ⟨1000, 0⟩ (.obj
      [("active".toList, .obj [("id".toList, .str "m2".toList),
          ("started".toList, .num 900), ("estMin".toList, .num 60)]),
       ("break".toList, .obj [("started".toList, .num 940),
          ("plannedMin".toList, .num 10), ("place".toList, .str "walk".toList)]),
       ("interrupt".toList, .obj [("started".toList, .num 950),
          ("id".toList, .str "m1".toList)]),
       ("lastHash".toList, .str "00000000000000ff".toList),
       ("yesterday".toList, .arr [.obj [("id".toList, .str "m1".toList),
          ("p".toList, .num 3)]])])).map (fun st =>
        (st.active, st.brk, st.interrupt, st.lastHash.map (fun h => h.val),
         st.yesterday.val.map (fun q => (q.1, q.2.val))))
      = .ok (some ⟨"m2".toList, ⟨900, 0⟩, 60, false⟩,
             some ⟨some ⟨940, 0⟩, 10, some BreakPlace.walk⟩,
             some ⟨some ⟨950, 0⟩, some "m1".toList⟩,
             some 255, [("m1".toList, 3)]) := by rfl

/-! ### `routines`' rejection theorems (R10) -/

/-- **A routine's `id` past the bound is refused**, at its position. -/
theorem readRoutine_refuses_a_long_id (i : Nat) (v : JVal) (id : Id)
    (hs : EmitWire.strAtP v "id" (PlannerRefusal.badRoutine i PlanKey.id) = .ok id)
    (h : CapWire.maxCandId < id.length) :
    readRoutine i v = .error (PlannerRefusal.badRoutine i PlanKey.id) := by
  simp only [readRoutine, hs, bind, Except.bind,
    EmitWire.idWithin_refuses_a_long_id (PlannerRefusal.badRoutine i PlanKey.id) id h]

/-- **A routine window past the calendar is refused**, through `EmitWire.secWithin`. -/
theorem readRoutine_refuses_a_window_past_the_calendar :
    readRoutine 1 (.obj [("id".toList, .str "lunch".toList),
      ("winLo".toList, .num 315537897600), ("winHi".toList, .num 0),
      ("durMin".toList, .num 30)])
      = .error (PlannerRefusal.badRoutine 1 PlanKey.winLo) := by rfl

/-- **A `durMin` past the fork's `u32` is refused**, through `EmitWire.u32Within`. -/
theorem readRoutine_refuses_a_duration_past_the_width (i : Nat) (v : JVal) (id : Id)
    (lo hi n : Nat)
    (hs : EmitWire.strAtP v "id" (PlannerRefusal.badRoutine i PlanKey.id) = .ok id)
    (hlen : id.length ≤ CapWire.maxCandId)
    (hin : EmitWire.optStrAtP v "inst" (PlannerRefusal.badRoutine i PlanKey.inst) = .ok none)
    (hlo : EmitWire.natAtP v "winLo" (PlannerRefusal.badRoutine i PlanKey.winLo) = .ok lo)
    (hlo' : EmitWire.secWithin (PlannerRefusal.badRoutine i PlanKey.winLo) lo = .ok lo)
    (hhi : EmitWire.natAtP v "winHi" (PlannerRefusal.badRoutine i PlanKey.winHi) = .ok hi)
    (hhi' : EmitWire.secWithin (PlannerRefusal.badRoutine i PlanKey.winHi) hi = .ok hi)
    (hd : EmitWire.natAtP v "durMin" (PlannerRefusal.badRoutine i PlanKey.durMin) = .ok n)
    (h : CapWire.maxRemaining < n) :
    readRoutine i v = .error (PlannerRefusal.badRoutine i PlanKey.durMin) := by
  simp only [readRoutine, hs, hin, hlo, hlo', hhi, hhi', hd, bind, Except.bind, Except.map,
    EmitWire.idWithin_accepts_at_the_bound (PlannerRefusal.badRoutine i PlanKey.id) id hlen,
    EmitWire.u32Within_refuses_past_the_width (PlannerRefusal.badRoutine i PlanKey.durMin) n h]
  rfl

/-- A real window instance reads, so the refusals above are not the only outcome. -/
theorem readRoutine_accepts_an_instance :
    readRoutine 0 (.obj [("id".toList, .str "lunch".toList),
      ("winLo".toList, .num 1000), ("winHi".toList, .num 2000),
      ("durMin".toList, .num 30), ("mandatory".toList, .bool true)])
      = .ok ⟨"lunch".toList, none, 1000, 2000, 30, true⟩ := by rfl

/-- **An absent `mandatory` is `false`**, which is §5.2's own default for an instance that does
not say it is mandatory. -/
theorem readRoutine_mandatory_is_absent_is_false :
    (readRoutine 0 (.obj [("id".toList, .str "lunch".toList), ("winLo".toList, .num 1000),
      ("winHi".toList, .num 2000), ("durMin".toList, .num 30)])).map (fun r => r.mandatory)
      = .ok false := by rfl

/-- The empty list reads. -/
theorem readRoutines_of_nil : readRoutines [] = .ok [] := rfl

/-- **Two instances read, at their positions.**  `readRoutines` came back **SURVIVED** at
`:= default` on `readRoutines_of_nil` alone: the empty list is what `default` answers. -/
theorem readRoutines_accepts_two_instances :
    readRoutines [.obj [("id".toList, .str "lunch".toList), ("winLo".toList, .num 1000),
        ("winHi".toList, .num 2000), ("durMin".toList, .num 30)],
      .obj [("id".toList, .str "shower".toList), ("winLo".toList, .num 3000),
        ("winHi".toList, .num 4000), ("durMin".toList, .num 20),
        ("mandatory".toList, .bool true)]]
      = .ok [⟨"lunch".toList, none, 1000, 2000, 30, false⟩,
             ⟨"shower".toList, none, 3000, 4000, 20, true⟩] := by rfl

/-! ### `overrides`' rejection theorems (R10) -/

/-- **An override's minutes past the fork's `u32` is refused.** -/
theorem readOverrides_refuses_an_estimate_past_the_width :
    readOverrides (.obj [("est".toList, .arr [.obj [("id".toList, .str "m1".toList),
      ("min".toList, .num 4294967296)]])])
      = .error (PlannerRefusal.badOverride PlanKey.est) := by rfl

/-- **A `drop` entry that is not a string is refused by name**, never skipped. -/
theorem readOverrides_refuses_a_drop_that_is_not_an_id :
    readOverrides (.obj [("drop".toList, .arr [.num 3])])
      = .error (PlannerRefusal.badOverride PlanKey.drop) := by rfl

/-- **A `drop` id past the bound is refused**, through `EmitWire.idWithin`. -/
theorem readOverrides_refuses_a_long_drop_id (v : JVal) (s : List Char)
    (he : readOverrideList v "est" PlanKey.est = .ok [])
    (hx : readOverrideList v "extra" PlanKey.extra = .ok [])
    (hd : readOverrideList v "drop" PlanKey.drop = .ok [.str s])
    (h : CapWire.maxCandId < s.length) :
    readOverrides v = .error (PlannerRefusal.badOverride PlanKey.drop) := by
  have hdrop : readDropIds [.str s] = .error (PlannerRefusal.badOverride PlanKey.drop) := by
    simp only [readDropIds, List.mapM, List.mapM.loop,
      EmitWire.idWithin_refuses_a_long_id (PlannerRefusal.badOverride PlanKey.drop) s h]
    rfl
  simp only [readOverrides, he, hx, hd, bind, Except.bind, hdrop]
  rfl

/-- **More estimate overrides than the candidate cap is refused**, through
`Planner.mkOverrides?` — `Planner.maxCands`, not a number written here.  Stated over whatever
the three readers return, so it is a fact about the decoder and not about one JSON object. -/
theorem readOverrides_refuses_too_many_estimates (v : JVal) (estJ extraJ dropJ : List JVal)
    (est extra : List (Id × Nat)) (drop : List Id)
    (he : readOverrideList v "est" PlanKey.est = .ok estJ)
    (hx : readOverrideList v "extra" PlanKey.extra = .ok extraJ)
    (hd : readOverrideList v "drop" PlanKey.drop = .ok dropJ)
    (hme : estJ.mapM (readOverridePair PlanKey.est) = .ok est)
    (hmx : extraJ.mapM (readOverridePair PlanKey.extra) = .ok extra)
    (hmd : readDropIds dropJ = .ok drop)
    (h : Planner.maxCands < est.length) :
    readOverrides v = .error PlannerRefusal.tooManyOverrides := by
  simp only [readOverrides, he, hx, hd, bind, Except.bind, hme, hmx, hmd,
    Planner.mkOverrides?_refuses_too_many_estimates est extra drop h]
  rfl

/-- **And more drops than the cap**, through the same constructor's other rejection theorem. -/
theorem readOverrides_refuses_too_many_drops (v : JVal) (estJ extraJ dropJ : List JVal)
    (est extra : List (Id × Nat)) (drop : List Id)
    (he : readOverrideList v "est" PlanKey.est = .ok estJ)
    (hx : readOverrideList v "extra" PlanKey.extra = .ok extraJ)
    (hd : readOverrideList v "drop" PlanKey.drop = .ok dropJ)
    (hme : estJ.mapM (readOverridePair PlanKey.est) = .ok est)
    (hmx : extraJ.mapM (readOverridePair PlanKey.extra) = .ok extra)
    (hmd : readDropIds dropJ = .ok drop)
    (h : Planner.maxCands < drop.length) :
    readOverrides v = .error PlannerRefusal.tooManyOverrides := by
  simp only [readOverrides, he, hx, hd, bind, Except.bind, hme, hmx, hmd,
    Planner.mkOverrides?_refuses_too_many_drops est extra drop h]
  rfl

/-- The empty `overrides` object reads as the empty what-if. -/
theorem readOverrides_of_an_empty_object :
    (readOverrides (.obj [])).map (fun o => o.isEmpty) = .ok true := by rfl

/-- **An absent `overrides` is no what-if** — the field's own `none`. -/
theorem readOptOverrides_of_an_absent_key : readOptOverrides (.obj []) = .ok none := rfl

/-- **A present `overrides` reads**, which `readOptOverrides_of_an_absent_key` does not show:
that reader too came back **SURVIVED** at `:= default`, whose answer is the absence. -/
theorem readOptOverrides_accepts_a_what_if :
    (readOptOverrides (.obj [("overrides".toList, .obj
      [("est".toList, .arr [.obj [("id".toList, .str "m1".toList), ("min".toList, .num 90)]]),
       ("drop".toList, .arr [.str "m2".toList])])])).map
        (fun o => o.map (fun q => (q.estMin.val, q.extraMin.val, q.drop.val)))
      = .ok (some ([("m1".toList, 90)], [], ["m2".toList])) := by rfl

/-! ### `prio.batchMaxMin` — README gap 801's four lines, answered -/

/-- **A `batchMaxMin` past the fork's `u32` is refused** (R10), through `EmitWire.u32Within` —
which is `CapWire.maxRemaining` is `Look.maxPlanMinutes`, the width `config.rs:361` declares.
No new number and no new name (gap **1330**'s warning). -/
theorem readBatchMaxMin_refuses_past_the_width (cap pv : JVal) (n : Nat)
    (hp : EmitWire.optAtP cap "priority" PlannerRefusal.badBatchMaxMin = .ok (some pv))
    (hn : EmitWire.natAtP pv "batchMaxMin" PlannerRefusal.badBatchMaxMin = .ok n)
    (h : CapWire.maxRemaining < n) :
    readBatchMaxMin cap = .error PlannerRefusal.badBatchMaxMin := by
  simp only [readBatchMaxMin, hp, hn,
    EmitWire.u32Within_refuses_past_the_width PlannerRefusal.badBatchMaxMin n h]

/-- **An absent `priority` object is refused by name, never defaulted to §16's 20.**  A default
written here would be a second copy of `config.rs:371`, which is the defect this kernel is named
after; `CapWire.readPriority` defaults none of its own three either. -/
theorem readBatchMaxMin_refuses_an_absent_priority :
    readBatchMaxMin (.obj []) = .error PlannerRefusal.badBatchMaxMin := rfl

/-- And §16's shipped 20 reads, so the two refusals are not the only outcome. -/
theorem readBatchMaxMin_accepts_the_shipped_default :
    readBatchMaxMin (.obj [("priority".toList,
      .obj [("batchMaxMin".toList, .num 20)])]) = .ok 20 := by rfl

/-- **The guard is the fork's `u32` exactly**: 4,294,967,295 reads and 4,294,967,296 does not,
so the bound is where `config.rs:361` puts it and not one step either side. -/
theorem readBatchMaxMin_is_the_forks_u32_width :
    readBatchMaxMin (.obj [("priority".toList,
        .obj [("batchMaxMin".toList, .num 4294967295)])]) = .ok 4294967295
      ∧ readBatchMaxMin (.obj [("priority".toList,
        .obj [("batchMaxMin".toList, .num 4294967296)])])
          = .error PlannerRefusal.badBatchMaxMin := ⟨rfl, rfl⟩

/-! ### The section as a whole -/

/-- **The empty section is the empty planner input** — nothing running, no instance due, no
what-if — so every refusal above is a refusal of something a host actually sent. -/
theorem readPlannerSection_of_an_empty_object (now : Cal.Instant) :
    readPlannerSection now (.obj [])
      = .ok ⟨RuntimeIn.empty, [], none⟩ := rfl

/-- **A `routines` key that is not an array is refused by name**, never read as none. -/
theorem readPlannerSection_refuses_a_routines_that_is_not_an_array (now : Cal.Instant) :
    readPlannerSection now (.obj [("routines".toList, .num 3)])
      = .error (PlannerRefusal.badRoutine 0 PlanKey.routines) := rfl

/-! ## The entry — R9's one export, one section further along

**A decoder with no caller is the defect this campaign is about.**  `Emit.lean` landed at W-22
with none and its own header says what that cost; this section will not repeat it.  So the
`planner` section is **read on every call that carries one**, and a section that does not decode
refuses the call by name — through the FFI, today, before anything consumes the values.

**What it does NOT do yet, said plainly.**  A section that *does* decode leaves the response
byte-for-byte what `EmitWire.runRows` answered: `runPlanner_with_a_readable_section_answers_as
_runRows` is that as a theorem rather than as prose.  Building `Planner.PlanReq` from these
values and emitting `Planner.dayPlan`'s seven keys is the other half of D48 and is **not here** —
README gap **1667**, with the two obstacles gaps **1668** and **1669** name.  What this half
buys is R10: every bound in the table at the top of this file is now on a path a host can reach,
and `tm/tests/kernel_planner_wire.rs` reaches it.

**`now` is the capacity section's `at`, through `CapWire.readAt`** — the kernel's one reader of
that key, and the instant `Look.Today.now` itself is built from at step L9.  It is **not** the
request's top-level `now`: `Boundary.parseClock` reads that as a `Day` through
`Field.parseDate`, and §9's three records are `wf` against an *instant*, so taking the day
number for an instant would be a unit error the types happen not to catch (both are `Nat`).
Reading `at` here is one more *call* of one decoder, not a second decoding of one value — and
its refusal branch is unreachable for that reason, which is README gap **1672** and is stated
as a theorem below rather than left to be found. -/

/-- **The request, with its `planner` section.**  Without one this is `EmitWire.runRows`, byte
for byte.  With one: `runRows` answers first, so every refusal that stood before this step still
comes first and in the same order; then the request's `now`, then the section. -/
def runPlanner (j : JVal) : Except JVal JVal :=
  match jget j "planner" with
  | .error e => .error (jsonErr e)
  | .ok none => EmitWire.runRows j
  | .ok (some sec) =>
    match EmitWire.runRows j with
    | .error e => .error e
    | .ok r =>
      match jget j "capacity" with
      | .error _ => .error (plannerRefusalJson PlannerRefusal.capacityAbsent)
      | .ok none => .error (plannerRefusalJson PlannerRefusal.capacityAbsent)
      | .ok (some cap) =>
        match CapWire.readAt cap with
        | .error e => .error (CapWire.refusalJson e)
        | .ok now =>
          match readPlannerSection now sec with
          | .error x => .error (plannerRefusalJson x)
          | .ok _ =>
            match readBatchMaxMin cap with
            | .error x => .error (plannerRefusalJson x)
            | .ok _ => .ok r

/-- **The response value for a request's bytes**, `EmitWire.respondRows`' shape over
`runPlanner`. -/
def respondPlanner (input : List Char) : JVal :=
  match jparse input with
  | .error e => jsonErr s!"bad json: {jerrText e}"
  | .ok j =>
    match runPlanner j with
    | .error e => e
    | .ok r    => r

/-- What the FFI runs. -/
def callPlanner (input : String) : String := String.ofList (jemit (respondPlanner input.toList))

/-- **The one export** (R9), moved here from `EmitWire.callExport` so that the planner's inputs
can reach it.  The symbol, the shim and the `String → String` signature are unchanged. -/
@[export tm_kernel_call]
def callExport (input : String) : String := callPlanner input

/-! ### The entry's laws -/

/-- **A request with no `planner` section is answered exactly as before.** -/
theorem runPlanner_without_a_planner_section_is_runRows (j : JVal)
    (h : jget j "planner" = .ok none) : runPlanner j = EmitWire.runRows j := by
  simp [runPlanner, h]

/-- And its bytes are `EmitWire.callRows`'. -/
theorem callPlanner_without_a_planner_section_is_callRows (input : String)
    (j : JVal) (hp : jparse input.toList = .ok j) (h : jget j "planner" = .ok none) :
    callPlanner input = EmitWire.callRows input := by
  simp only [callPlanner, EmitWire.callRows, respondPlanner, EmitWire.respondRows, hp,
    runPlanner_without_a_planner_section_is_runRows j h]
  rfl

/-- **A readable `planner` section changes no byte of the answer** — the response half of D48 is
owed (README gap **1667**) and this is that owed-ness as a theorem, so a later step deleting it
is the step that pays. -/
theorem runPlanner_with_a_readable_section_answers_as_runRows (j sec cap r : JVal) (b : Nat)
    (now : Cal.Instant) (q : PlannerIn)
    (hp : jget j "planner" = .ok (some sec)) (hr : EmitWire.runRows j = .ok r)
    (hc : jget j "capacity" = .ok (some cap)) (hn : CapWire.readAt cap = .ok now)
    (hs : readPlannerSection now sec = .ok q) (hb : readBatchMaxMin cap = .ok b) :
    runPlanner j = .ok r := by
  simp only [runPlanner, hp, hr, hn, hs, hc, hb]

/-- **An unreadable `at` keeps the capacity section's OWN name**, not a second one —
`CapWire.readAt` is the one reader of that key and `CapWire.refusalJson` is the shape its
refusals already go out in.

**And this branch is unreachable through `runPlanner`**, said here rather than discovered
later: `EmitWire.runRows` answers first, `runCap` inside it runs `readCapacityZ`, and
`readCapacityZ` calls this same `readAt` and refuses `badAt` — so a request that reaches the
line below has a capacity section the kernel already accepted.  It is `runLoad`'s situation one
section along (README gap **1325**: *"a cost and not a second reading — one `runLoad`, called
twice"*), and the honest removal is `runCapZ` handing its decoded `CapReq` out rather than only
its bytes.  README gap **1672**; `tm/tests/kernel_planner_wire.rs` asserts the ordering that
makes it unreachable rather than asserting a refusal no host can produce (AGENTS §9.2). -/
theorem runPlanner_keeps_the_capacity_sections_name_for_an_unreadable_at
    (j sec cap r : JVal) (e : CapWire.Refusal)
    (hp : jget j "planner" = .ok (some sec)) (hr : EmitWire.runRows j = .ok r)
    (hc : jget j "capacity" = .ok (some cap)) (hn : CapWire.readAt cap = .error e) :
    runPlanner j = .error (CapWire.refusalJson e) := by
  simp only [runPlanner, hp, hr, hc, hn]

/-- **And a section that does not decode refuses the whole call, by its own name** — the sentence
that makes every bound in this module reachable from the FFI. -/
theorem runPlanner_refuses_a_section_the_decoder_refuses (j sec cap r : JVal)
    (now : Cal.Instant) (x : PlannerRefusal)
    (hp : jget j "planner" = .ok (some sec)) (hr : EmitWire.runRows j = .ok r)
    (hc : jget j "capacity" = .ok (some cap)) (hn : CapWire.readAt cap = .ok now)
    (hs : readPlannerSection now sec = .error x) :
    runPlanner j = .error (plannerRefusalJson x) := by
  simp only [runPlanner, hp, hr, hc, hn, hs]

/-- **A `planner` section without a `capacity` section is refused by name** — `PlanReq.look`
and `prio`'s five values are the capacity section's, so the request could not be assembled. -/
theorem runPlanner_refuses_a_planner_section_without_a_capacity (j sec r : JVal)
    (hp : jget j "planner" = .ok (some sec)) (hr : EmitWire.runRows j = .ok r)
    (hc : jget j "capacity" = .ok none) :
    runPlanner j = .error (plannerRefusalJson PlannerRefusal.capacityAbsent) := by
  simp only [runPlanner, hp, hr, hc]

/-- **And a `batchMaxMin` the decoder refuses refuses the call** — README gap 801's value with a
caller, which is what makes its bound more than a definition. -/
theorem runPlanner_refuses_a_batch_max_min_the_decoder_refuses (j sec cap r : JVal)
    (now : Cal.Instant) (q : PlannerIn) (x : PlannerRefusal)
    (hp : jget j "planner" = .ok (some sec)) (hr : EmitWire.runRows j = .ok r)
    (hc : jget j "capacity" = .ok (some cap)) (hn : CapWire.readAt cap = .ok now)
    (hs : readPlannerSection now sec = .ok q) (hb : readBatchMaxMin cap = .error x) :
    runPlanner j = .error (plannerRefusalJson x) := by
  simp only [runPlanner, hp, hr, hc, hn, hs, hb]

/-- **The export is `callPlanner`.** -/
theorem callExport_is_callPlanner (input : String) : callExport input = callPlanner input := rfl

end PlanWire
end Tm
