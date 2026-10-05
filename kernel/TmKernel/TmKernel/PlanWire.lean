import TmKernel.EmitWire
import TmKernel.PlanDiff
import TmKernel.PlanOnce
/-! # `PlanWire.lean` — the PLANNER's inputs cross the wire (stage 6, W-27, D48, README gaps 1431/801)

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
| `active.estMin` | `Look.maxPlanMinutes` (the fork's `u32`, D81 gap 3902), through the wf predicate | `Planner.mkActive?` | `readActive_refuses_an_estimate_past_the_width` |
| `active.started`, `brk.started`, `interrupt.started`, a routine's `winLo`/`winHi` | `Cal.Instant.wf` | `Cal.mkInstant?`, through `EmitWire.secWithin` | `instantWithin_refuses_past_the_calendar`, `readRoutine_refuses_a_window_past_the_calendar` |
| `active.started`, `interrupt.started` after `now` | NONE since W-41: D78 plans both as fork 4748911 does, from `now` | — | `readActive_accepts_a_start_after_now`, `readInterrupt_accepts_a_start_after_now` |
| `brk.plannedMin` | `Look.maxPlanMinutes` (D81 gap 3902), through the wf predicate | `Planner.mkBreak?` | `readBreak_refuses_a_break_past_the_width` |
| `brk.started ≤ now` | `Planner.BreakState.wf` (D81: the host never sends one after `now`) | `Planner.mkBreak?` | `readBreak_refuses_a_start_after_now` |
| `active.workedMin` | `Look.maxPlanMinutes` (W-41, the width again) | `Planner.workedOf?` | `readOptWorked_refuses_a_reading_past_the_width` |
| the day's evening (D80 (a), P71) | `LogStamp.yearEnd` | `Planner.PlanReq.eveningInsideTheCalendar`, in `planReqRefusal` | `planReqRefusal_names_an_evening_past_the_calendar` |
| a candidate's wire `ci` (D80 (b), P72) | the plan's `ci` for the item | `Planner.PlanReq.ciDisagreement`, in `planReqRefusal` | `planReqRefusal_names_a_candidate_whose_ci_disagrees` |
| `lastHash` | `Planner.hashBound`, exactly `hashHexLen` hex digits | `Planner.mkHash?` | `readHash_refuses_a_short_digest` |
| a `yesterday` priority | `Fin 8`, through the one reader of a stored `p` | `Planner.mkYesterday?` | `readYesterday_refuses_a_priority_past_seven` |
| the `yesterday` list | `Planner.maxCands` | `Planner.mkYesterday?` | `readYesterday_refuses_past_the_cap` |
| a routine's `durMin`, an override's minutes | `CapWire.maxRemaining` (fork `u32`) | `EmitWire.u32Within` | `readRoutine_refuses_a_duration_past_the_width`, `readOverrides_refuses_an_estimate_past_the_width` |
| the override lists | `Planner.maxCands` | `Planner.mkOverrides?` | `readOverrides_refuses_too_many_estimates`, `readOverrides_refuses_too_many_drops` |
| `prio.batchMaxMin` | `CapWire.maxRemaining` (fork `u32`) | `EmitWire.u32Within` | `readBatchMaxMin_refuses_past_the_width` |
| the routine list, and each instance's rule | `Planner.maxCands`, `Planner.mkRoutine?` | `Planner.mkRoutines?` | already proved — `mkRoutines?_refuses_too_many`, and `PlannerWit.mkPlanReq?_refuses_a_routine_the_rule_refuses` carries it out |

**`batchMaxMin` takes the fork's `u32` and not the day's 1,440.**  `config.rs:361` declares `pub batch_max_min: u32`;
a tighter bound would be a *divergence from the comparand* (D21/D22/D23) owing a parity number.  `EmitWire.u32Within`
is the guard and `CapWire.maxRemaining` is `Look.maxPlanMinutes` — one function, one number, no third name.

## §10.3's family, and the two names that are deliberately NOT declared

Design §10.3 reserves `planRefusal.*` for `badState`, badWindow, badBudget, `badActive`, `badBreak`, `badInterrupt`,
`badHash`, `badOverride` and tooManyCands — three spelled without backticks because nothing declares them.

**The type is `PlannerRefusal` and deliberately NOT PlanRefusal.**  Four ledger sentences and `Planner.dayPlan`'s own
header cite PlanRefusal as a type that **does not exist**, because `dayPlan` is total (D28) and has no error type —
`kernel/citations-allow.txt` carries the name under *"names D28 says do NOT exist"* with five counted citations.  A type
of that name here would make five committed sentences false while `dayPlan`'s signature was unchanged, a ledger rot
check 8 would answer by going **quieter**.  So the wire key is `planner`, the type is `PlannerRefusal`, and PlanRefusal
still does not exist.

Seven of §10.3's nine names are below.  **badWindow and badBudget are not, and their absence is
the point**:
`Planner.PlanReq` has no window field and no budget field — `PlanReq.window` is
the stored window (crossing midnight as the fork's planner reads it, gap 3341) or `Look.day0Window r.look`, and `PlanReq.budgetBlocks` is the stored one
or `Look.budgetOf`, both *views* (`PlanReq.window_crosses_midnight_as_the_forks_planner_reads_it`).  There is nothing
on this wire for either name to be about, so declaring them would put two constructors in `PlannerRefusal` that **no
input can reach** — AGENTS §9.2's disguised gap, where R10 is supposed to prevent it.  tooManyCands is likewise absent:
the candidate cap is `capacity.candidates`', refused there as `Boundary.Refusal.tooManyCandidates`.  README gap **1664**.

**`EmitWire.RowRefusal` is deliberately not this family** and this module does not rename it:
the two live in one `plan` object with disjoint keys, exactly as `EmitWire.lean`'s header says
R3 would arrange them, and `Planner.dayPlan` stays **total** (D28) — nothing here makes it an
`Except`, and a refusal in this module is a refusal to *build the request*, never a refusal by
the planner.

## Reusing `EmitWire`'s readers rather than writing them again

`EmitWire.asPlan` and the eight readers over it (`natAtP`, `strAtP`, `arrAtP`, `optAtP`, `flagAtP`, `optNatAtP`,
`optStrAtP`) and the three guards (`idWithin`, `u32Within`, `secWithin`) were typed to `RowRefusal`.  They are now
**polymorphic in the refusal** (`{ρ : Type}`), which is the smallest edit that lets this section reuse them by name
instead of copying nine JSON shapes and three bounds one module along.  Every existing call site and every
existing theorem is unchanged in meaning: `ρ` unifies with `RowRefusal` exactly where it did before, and
`asPlan_keeps_the_value` / `asPlan_renames_a_refusal` are now *stronger* statements (∀ ρ) that imply the ones they
replace (D5).
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
  | overtime | blocks | grown | remaining | workedMin
  /-- **The record's own well-formedness**, when `Planner.mkActive?` or `mkBreak?` answers `none` (and the
  interruption's, until D78 took its constructor away at W-41).  Those answer `Option` and not a named error, so the
  wire can say *which record* the planner could not hold and not *which clause* of its `wf` failed — README gap
  **1665**, and the reason this key is not one of the field names above. -/
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
  | .overtime => "overtime" | .blocks => "blocks" | .grown => "grown" | .remaining => "remaining"
  | .workedMin => "workedMin"

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
  /-- **The section needs this call's own replay** (D9, D24): `Planner.PlanReq.run` is a
  `Seal.Run`, and the seam carries one only on a request whose `log` section **resumed and asked
  for facts** (`Boundary.LogReq.seamRun`).  A request that sent no `log` section, or sent one
  that asked for no facts, is refused by name rather than planned against a blank — D24's own
  rule for the wake (`wakeWithoutLog`), one section along. -/
  | runAbsent
  /-- **The wall index the capacity section decoded is not this plan's** (README gap 346, from
  the wire's side).  `PlannerWit.mkPlanReq?` refuses the same disagreement as `.walls`; here it
  is checked rather than assumed, because `Planner.PlanReq` has no invariant that carries it. -/
  | wallsDisagree
  /-- **More candidates than `Planner.maxCands`** — and this is deliberately **not** §10.3's
  tooManyCands, which is the *capacity* section's and is refused as
  `Boundary.CapWire.Refusal.tooManyCandidates` before this section is read at all.  This is the
  **assembler's** cap: `Capped.ofList?` is `PlanReq.cands`' one constructor and it refuses past
  `Planner.maxCands`, while the section that produced the list guarded at
  `CapWire.maxCandidates`.  README gap **1330** records that those are one number under two
  names; `the_two_candidate_caps_are_one_number` below is the first place anything states it, and
  until a lemma carries `readCands`' guard to this constructor the branch stays. -/
  | candsPastCap
  /-- **A window instance `Planner.mkRoutine?` refuses**, carrying its name out (AGENTS §5.3:
  the rule is the planner's and this constructor does not restate it). -/
  | routineRefused (e : Planner.RoutineErr)
  /-- **A key of the `overtime` object** (W-34): §9.1's "x extend +N block" what-if. -/
  | badOvertime (k : PlanKey)
  /-- **D80 (a)** (P71): the day's evening runs past the calendar's last second (`Planner.PlanReq.eveningInsideTheCalendar`). -/
  | eveningPastTheCalendar
  /-- **D80 (b)** (P72): a candidate whose wire `ci` is not the plan's — the id, the wire's value, the plan's (or none). -/
  | ciDisagrees (i : Id) (wire : Fin 6) (plan : Option (Fin 6))
deriving DecidableEq, Repr

/-- `Planner.RoutineErr`'s six names, spelled where the wire can read them, **each with the id
it is about** — five of the six are about one window instance and a host told only the rule
cannot tell which instance it sent was refused.  The rule that produces each is
`Planner.mkRoutine?`'s; this only names it (AGENTS §5.3). -/
def routineErrName : Planner.RoutineErr → String
  | .unknownItem id => s!"unknownItem {String.ofList id}"
  | .undeclaredWindow id => s!"undeclaredWindow {String.ofList id}"
  | .emptyWindow id => s!"emptyWindow {String.ofList id}"
  | .pastTheHorizon id => s!"pastTheHorizon {String.ofList id}"
  | .noMinutes id => s!"noMinutes {String.ofList id}"
  | .tooManyRoutines => "tooManyRoutines"

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
  | .runAbsent => "runAbsent"
  | .wallsDisagree => "wallsDisagree"
  | .candsPastCap => "candsPastCap"
  | .routineRefused e => s!"routineRefused {routineErrName e}"
  | .badOvertime k => s!"badOvertime {k.name}"
  | .eveningPastTheCalendar => "eveningPastTheCalendar"
  | .ciDisagrees i w p => s!"ciDisagrees {String.ofList i} wire {w.val} plan {(p.map (fun c => toString c.val)).getD "none"}"

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
def readActive (v : JVal) : Except PlannerRefusal ActiveBlock := do
  let idS ← EmitWire.strAtP v "id" (PlannerRefusal.badActive PlanKey.id)
  let id ← EmitWire.idWithin (PlannerRefusal.badActive PlanKey.id) idS
  let secN ← EmitWire.natAtP v "started" (PlannerRefusal.badActive PlanKey.started)
  let started ← instantWithin (PlannerRefusal.badActive PlanKey.started) secN
  let estMin ← EmitWire.natAtP v "estMin" (PlannerRefusal.badActive PlanKey.estMin)
  let paused ← EmitWire.flagAtP v "paused" (PlannerRefusal.badActive PlanKey.paused)
  match Planner.mkActive? ⟨id, started, estMin, paused⟩ with
  | some a => pure a.val
  | none => throw (PlannerRefusal.badActive PlanKey.wf)

/-- An absent or `null` `active` is nothing running. -/
def readOptActive (v : JVal) : Except PlannerRefusal (Option ActiveBlock) :=
  match EmitWire.optAtP v "active" (PlannerRefusal.badState PlanKey.active) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some w) => (readActive w).map some

/-- The four `--where` words of fork 4748911's `BreakPlace` (`tm/src/tui/app.rs`'s; since W-41 track T the host's one table is `tm_core::store::BreakPlace`,
and `tm/tests/cli_break_place.rs` sends every one of its words through this reader — the W-41 repair, README gap 4145).  An unknown word is refused by name, never defaulted (AGENTS §5.7). -/
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

/-- `state.interrupt`.  §9's open interruption is an ad-hoc wall from `t_i` to `now` and both of its fields are
optional.  **No constructor since W-41**: Planner.mkInterrupt? bounded the start by `now` and nothing else, and D78
reads a start after `now` as fork 4748911 does — no wall at all (`Planner.interruptRows`) — so each field keeps its own
reader's bound (`instantWithin`, `EmitWire.idWithin`) and the record is what they read. -/
def readInterrupt (v : JVal) : Except PlannerRefusal InterruptState := do
  let secO ← EmitWire.optNatAtP v "started" (PlannerRefusal.badInterrupt PlanKey.started)
  let started ← match secO with
    | none => pure none
    | some n => (instantWithin (PlannerRefusal.badInterrupt PlanKey.started) n).map some
  let idO ← EmitWire.optStrAtP v "id" (PlannerRefusal.badInterrupt PlanKey.id)
  let id ← match idO with
    | none => pure none
    | some s => (EmitWire.idWithin (PlannerRefusal.badInterrupt PlanKey.id) s).map some
  pure ⟨started, id⟩
def readOptInterrupt (v : JVal) : Except PlannerRefusal (Option InterruptState) :=
  match EmitWire.optAtP v "interrupt" (PlannerRefusal.badState PlanKey.interrupt) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some w) => (readInterrupt w).map some
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
/-- `state.active.workedMin`, the host's worked minutes (W-36, gap 2920), through `Planner.workedOf?`; absent is `none`. -/
def readOptWorked (sec : JVal) : Except PlannerRefusal (Option (Fin (Look.maxPlanMinutes + 1))) :=
  match EmitWire.optAtP sec "active" (PlannerRefusal.badState PlanKey.active) with
  | .ok (some a) => match EmitWire.optNatAtP a "workedMin" (PlannerRefusal.badActive PlanKey.workedMin) with
    | .ok (some n) => match Planner.workedOf? n with | some w => .ok (some w) | none => .error (PlannerRefusal.badActive PlanKey.workedMin)
    | .ok none => .ok none | .error e => .error e
  | .ok none => .ok none | .error e => .error e
/-- **§9's five rows.**  Every one is optional and every absence is the field's own empty. -/
def readState (now : Cal.Instant) (sec : JVal) : Except PlannerRefusal RuntimeIn := do
  let active ← readOptActive sec
  let brk ← readOptBreak now sec
  let interrupt ← readOptInterrupt sec
  let lastHash ← readHash sec
  let ys ← match ← EmitWire.optAtP sec "yesterday" (PlannerRefusal.badState PlanKey.yesterday) with
    | none => pure []
    | some (.arr xs) => pure xs
    | some _ => throw (PlannerRefusal.badState PlanKey.yesterday)
  let yesterday ← readYesterday ys
  pure ⟨active, brk, interrupt, lastHash, yesterday, ← readOptWorked sec⟩
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
theorem readActive_refuses_a_long_id (v : JVal) (id : Id)
    (hs : EmitWire.strAtP v "id" (PlannerRefusal.badActive PlanKey.id) = .ok id)
    (h : CapWire.maxCandId < id.length) :
    readActive v = .error (PlannerRefusal.badActive PlanKey.id) := by
  simp only [readActive, hs, bind, Except.bind,
    EmitWire.idWithin_refuses_a_long_id (PlannerRefusal.badActive PlanKey.id) id h]

/-- **An `active.started` past the calendar is refused**, through `Cal.mkInstant?`. -/
theorem readActive_refuses_a_start_past_the_calendar (v : JVal) (id : Id)
    (n : Nat) (hs : EmitWire.strAtP v "id" (PlannerRefusal.badActive PlanKey.id) = .ok id)
    (hlen : id.length ≤ CapWire.maxCandId)
    (hn : EmitWire.natAtP v "started" (PlannerRefusal.badActive PlanKey.started) = .ok n)
    (h : Cal.mkInstant? n 0 = none) :
    readActive v = .error (PlannerRefusal.badActive PlanKey.started) := by
  simp only [readActive, hs, hn, bind, Except.bind,
    EmitWire.idWithin_accepts_at_the_bound (PlannerRefusal.badActive PlanKey.id) id hlen,
    instantWithin_refuses_past_the_calendar (PlannerRefusal.badActive PlanKey.started) n h]

/-- **A running block that started after `now` is READ since W-41** (the owner's D78; README gap 2874's input 1): the
reader takes no `now` at all, so readActive_refuses_a_start_after_now — `badActive wf` for a start after `now` — is
refuted, and §8.2 plans the block from `now` as fork 4748911 does (`PlannerWit`'s W-41 block computes the day).  A
start of 1,010 reads whatever `now` the request carries; at a `now` of 1,000 it is the ten seconds ahead D78 names. -/
theorem readActive_accepts_a_start_after_now :
    readActive (.obj [("id".toList, .str "m2".toList), ("started".toList, .num 1010),
      ("estMin".toList, .num 60)]) = .ok ⟨"m2".toList, ⟨1010, 0⟩, 60, false⟩ := by rfl

/-- **An `estMin` past the host's width is refused**, through the same constructor — `Look.maxPlanMinutes`, the
fork's `u32` (D81 gap 3902), is the bound, reused, and this module does not write a second one. -/
theorem readActive_refuses_an_estimate_past_the_width (v : JVal) (id : Id)
    (n est : Nat) (paused : Bool) (i : Cal.VInstant)
    (hs : EmitWire.strAtP v "id" (PlannerRefusal.badActive PlanKey.id) = .ok id)
    (hlen : id.length ≤ CapWire.maxCandId)
    (hn : EmitWire.natAtP v "started" (PlannerRefusal.badActive PlanKey.started) = .ok n)
    (hi : Cal.mkInstant? n 0 = some i)
    (he : EmitWire.natAtP v "estMin" (PlannerRefusal.badActive PlanKey.estMin) = .ok est)
    (hp : EmitWire.flagAtP v "paused" (PlannerRefusal.badActive PlanKey.paused) = .ok paused)
    (h : Look.maxPlanMinutes < est) :
    readActive v = .error (PlannerRefusal.badActive PlanKey.wf) := by
  simp only [readActive, hs, hn, he, hp, bind, Except.bind,
    EmitWire.idWithin_accepts_at_the_bound (PlannerRefusal.badActive PlanKey.id) id hlen,
    instantWithin_accepts_a_representable_second (PlannerRefusal.badActive PlanKey.started) n i hi,
    Planner.mkActive?_refuses_an_estimate_past_the_width ⟨id, ⟨i.val.sec, 0⟩, est, paused⟩ h]
  rfl

/-- **An `estMin` past the day is READ since W-41**: readActive_refuses_an_estimate_past_the_day is refuted at
`tm extend 24h`'s 1,500 minutes, which fork 4748911 plans (D81 gap 3902). -/
theorem readActive_reads_an_estimate_past_the_day :
    readActive (.obj [("id".toList, .str "m2".toList), ("started".toList, .num 900),
      ("estMin".toList, .num 1500)]) = .ok ⟨"m2".toList, ⟨900, 0⟩, 1500, false⟩ := by rfl

/-- And a real running block reads, so none of the refusals above is the only outcome
(AGENTS §5.8), and the fields land where they say they do — the start a second count, the
estimate a minute count, `paused` absent-is-`false`. -/
theorem readActive_accepts_a_running_block :
    readActive (.obj [("id".toList, .str "m2".toList),
      ("started".toList, .num 900), ("estMin".toList, .num 60)])
      = .ok ⟨"m2".toList, ⟨900, 0⟩, 60, false⟩ := by rfl

/-- **A `break` past the host's width is refused**, through `Planner.mkBreak?` (D81 gap 3902) — and the day's 1,441,
which readBreak_refuses_a_break_longer_than_a_day refused until W-41, is read (that theorem, refuted). -/
theorem readBreak_refuses_a_break_past_the_width :
    readBreak ⟨1000, 0⟩ (.obj [("plannedMin".toList, .num 4294967296)])
      = .error (PlannerRefusal.badBreak PlanKey.wf) ∧
    readBreak ⟨1000, 0⟩ (.obj [("plannedMin".toList, .num 1441)]) = .ok ⟨none, 1441, none⟩ := by
  constructor <;> rfl

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

/-- **A break that started after `now` is refused**, through `Planner.mkBreak?` (the other clause of its `wf`, under
`PlanKey.wf`).  D81 keeps it: the host reads a running break's start as the latest instant at or before `now`. -/
theorem readBreak_refuses_a_start_after_now :
    readBreak ⟨1000, 0⟩ (.obj [("started".toList, .num 1001),
      ("plannedMin".toList, .num 10)])
      = .error (PlannerRefusal.badBreak PlanKey.wf) := by rfl

/-- A real break reads. -/
theorem readBreak_accepts_a_running_break :
    readBreak ⟨1000, 0⟩ (.obj [("started".toList, .num 900),
      ("plannedMin".toList, .num 10), ("place".toList, .str "walk".toList)])
      = .ok ⟨some ⟨900, 0⟩, 10, some BreakPlace.walk⟩ := by rfl

/-- **An interruption that started after `now` is READ since W-41** (D78): readInterrupt_refuses_a_start_after_now is
refuted — the reader has no `now` to refuse it against, and §8.2 step 1 draws it as the fork does: not at all. -/
theorem readInterrupt_accepts_a_start_after_now :
    readInterrupt (.obj [("started".toList, .num 1001)]) = .ok ⟨some ⟨1001, 0⟩, none⟩ := by rfl

/-- **An interruption's `id` past the bound is refused**, through `EmitWire.idWithin`. -/
theorem readInterrupt_refuses_a_long_id (v : JVal) (id : Id)
    (hs : EmitWire.optNatAtP v "started" (PlannerRefusal.badInterrupt PlanKey.started) = .ok none)
    (hi : EmitWire.optStrAtP v "id" (PlannerRefusal.badInterrupt PlanKey.id) = .ok (some id))
    (h : CapWire.maxCandId < id.length) :
    readInterrupt v = .error (PlannerRefusal.badInterrupt PlanKey.id) := by
  simp only [readInterrupt, hs, hi, bind, Except.bind, Except.map,
    EmitWire.idWithin_refuses_a_long_id (PlannerRefusal.badInterrupt PlanKey.id) id h]
  rfl

/-- A real interruption reads. -/
theorem readInterrupt_accepts_an_open_interruption :
    readInterrupt (.obj [("started".toList, .num 900),
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

**A decoder with no caller is the defect this campaign is about** (`Emit.lean` landed at W-22
with none), so the `planner` section is **read on every call that carries one**, and a section
that does not decode refuses the call by name, before anything consumes the values.  **Since W-28 the call ANSWERS**: `Planner.dayPlan`'s seven keys go out
beside `rows` (README gap **1667**).  The two obstacles W-27 priced are gone rather than worked
around: gap **1668** needs no import of `PlannerWit.mkPlanReq?`, because `planReqOf` hands over
values this call's own readers produced; and gap **1669** is gone because `Boundary.CapParts`
hands out the loaded `WfPlan` itself, so no document is read twice. -/

/-! ## The response — design §10.2's `plan` keys (D48's RESPONSE half, README gap 1667)

`EmitWire.withPlan` writes `rows` into the `plan` object; the seven below are `Planner.dayPlan`'s
answer for a day the **kernel** planned, in the same object under disjoint keys
(`the_plan_objects_keys_are_disjoint`), so `tm/tests/planner_invariants.rs` can ask the kernel for
a day instead of asking it to render the fork's.  **Every value is a field or view of
`Planner.DayPlan`** and nothing here recomputes one: `planJson_*_is_the_days` are each `rfl`.
-/

/-- The seven keys, in design §10.2's order. -/
def planKeys : List (List Char) :=
  ["day".toList, "window".toList, "budgetBlocks".toList, "segments".toList,
   "diagnostics".toList, "priorities".toList, "hash".toList]

/-- `SegKind`'s eleven names — **`EmitWire.readKind`'s own**, so the section that reads a segment and the key that
writes one spell every kind the same way (`readKind_reads_back_every_kind_it_writes`). -/
def kindName : Planner.SegKind → List Char
  | .block => "block".toList
  | .batch _ => "batch".toList
  | .brk => "break".toList
  | .routine => "routine".toList
  | .wall => "wall".toList
  | .rest => "rest".toList
  | .optional => "optional".toList
  | .windDown => "wind-down".toList
  | .sleep => "sleep".toList
  | .lost => "lost".toList
  | .ghost => "ghost".toList

/-- A batch's members; every other kind has none. -/
def batchOf : Planner.SegKind → List JVal
  | .batch ids => ids.val.map JVal.str
  | _ => []

/-- A kind, as the `plan` section's segment object carries it: the name, and the members a
batch has.  `EmitWire.readKind` reads exactly these two keys. -/
def kindJson (k : Planner.SegKind) : JVal :=
  .obj [("kind".toList, .str (kindName k)), ("batch".toList, .arr (batchOf k))]

/-- An id that may be absent. -/
def optStr : Option Id → JVal
  | none => .null
  | some s => .str s

/-! **Two emitters this file used to declare are gone, and it declares none in their place**
(AGENTS §5.3, W-28 repair): optNum was `CapWire.optNatJson` character for character, and
pairJson `minutesJson` (its doc named a THIRD spelling, `CapWire.pairWith`).  A wire key emitted
by two functions is §5.3's bug; `segJson` calls the two that stood, and neither moved. -/

/-- The seven marks, in `EmitWire.readFlags`' order and under its keys. -/
def flagsJson (f : Planner.SegFlags) : JVal :=
  .obj [("done".toList, .bool f.done), ("current".toList, .bool f.current),
    ("underused".toList, .bool f.underused), ("hot".toList, .bool f.hot),
    ("mandatory".toList, .bool f.mandatory), ("deferred".toList, .bool f.deferred),
    ("open".toList, .bool f.isOpen)]

/-- **A note, named** (AGENTS §5.7).  `Planner.Note`'s twelve constructors each answer an object
whose `note` key is the constructor's own name and whose other keys are its fields — the prose
stays where the terminal is (D30 Q6) and the wire carries the name and the numbers. -/
def noteJson : Planner.Note → JVal
  | .travelDay => .obj [("note".toList, .str "travelDay".toList)]
  | .noPosition id durMin lo hi =>
      .obj [("note".toList, .str "noPosition".toList), ("id".toList, .str id),
        ("durMin".toList, .num durMin), ("lo".toList, .num lo), ("hi".toList, .num hi)]
  | .budgetSpent n =>
      .obj [("note".toList, .str "budgetSpent".toList), ("blocksDone".toList, .num n)]
  | .plannedOf a b =>
      .obj [("note".toList, .str "plannedOf".toList), ("planned".toList, .num a),
        ("total".toList, .num b)]
  | .bufferBefore id =>
      .obj [("note".toList, .str "bufferBefore".toList), ("id".toList, .str id)]
  | .travelDayWall => .obj [("note".toList, .str "travelDayWall".toList)]
  | .paused => .obj [("note".toList, .str "paused".toList)]
  | .interruption => .obj [("note".toList, .str "interruption".toList)]
  | .breakWhere t =>
      .obj [("note".toList, .str "breakWhere".toList), ("text".toList, .str t)]
  | .idleAttributed t =>
      .obj [("note".toList, .str "idleAttributed".toList), ("text".toList, .str t)]
  | .runningLeft m =>
      .obj [("note".toList, .str "runningLeft".toList), ("leftMin".toList, .num m)]
  | .soFar m => .obj [("note".toList, .str "soFar".toList), ("workedMin".toList, .num m)]

/-- **One row of the day**, in the shape `EmitWire.readSeg` reads — `start`, `stop`, `kind`, `batch`, `energy`, `item`,
`flags`, `planned`, `mult`, `note` — plus `inst`, the one field `readSeg` does **not** read (it builds every segment
with `inst := none`, because no cell of a row is about it).  So a day this key emits goes back through the `plan`
section unchanged except for that field, which `tm/tests/planner_invariants.rs` drives rather than assumes. -/
def segJson (s : Planner.WfSeg) : JVal :=
  .obj [("start".toList, .num s.val.start), ("stop".toList, .num s.val.stop),
    ("kind".toList, .str (kindName s.val.kind)),
    ("batch".toList, .arr (batchOf s.val.kind)),
    ("energy".toList, CapWire.optNatJson (s.val.energy.map Fin.val)),
    ("item".toList, optStr s.val.item),
    ("inst".toList, match s.val.inst with
      | none => .null
      | some p => .obj [("id".toList, .str p.1), ("inst".toList, .str p.2)]),
    ("flags".toList, flagsJson s.val.flags),
    ("planned".toList, CapWire.optNatJson s.val.planned),
    ("mult".toList, minutesJson s.val.mult),
    ("note".toList, match s.val.note with | none => .null | some n => noteJson n)]

/-- An `IdList`, whole. -/
def idsJson (c : Planner.IdList) : JVal := .arr (c.val.map JVal.str)

/-- The name `Planner.NoPlace`'s reason crosses the wire under (D67, P58; AGENTS §5.7): each constructor its own. -/
def noPlaceName : Planner.NoPlace → List Char | .noRunLeft => "noRunLeft".toList | .noSlotLeft => "noSlotLeft".toList | .budgetSpent => "budgetSpent".toList | .noSlotAdmits => "noSlotAdmits".toList
/-- §8.2 step 8's twelve fields under their own names, then the fork's three whole tuples `tm-core/src/emit.rs` prints (W-35, gaps 2640, 2743): `impossibleUntil` (`{id, shortMin, until}`, `YYYY-MM-DD`),
`underusedLevels` (`{id, energy, ci}`), `blockedDeps` (`{id, deps}`, each an `after:` spelling) — and since W-38 the kernel's `unplaced` (`{id, why}`, D67, P58), then `served`, §8.2 step 5's order (`{ix, id, ci}`, gap 3343).  The twelve keys' bytes are unchanged. -/
def diagJson (d : Planner.Diagnostics) : JVal :=
  .obj [("underused".toList, idsJson d.underused),
    ("aCapacityLost".toList, .num d.aCapacityLost),
    ("hot".toList, idsJson d.hot),
    ("impossible".toList,
      .arr (d.impossible.val.map (fun p =>
        .obj [("id".toList, .str p.1), ("shortMin".toList, .num p.2)]))),
    ("conflicts".toList,
      .arr (d.conflicts.val.map (fun p =>
        .obj [("a".toList, .str p.1), ("b".toList, .str p.2)]))),
    ("blocked".toList, idsJson d.blocked),
    ("deferred".toList, idsJson d.deferred),
    ("waiting".toList, idsJson d.waiting),
    ("notes".toList, .arr (d.notes.val.map noteJson)),
    ("droppedTail".toList, idsJson d.droppedTail),
    ("planHonesty".toList,
      .obj [("planned".toList, .num d.planHonesty.1), ("total".toList, .num d.planHonesty.2)]),
    ("restDebtMin".toList, .num d.restDebtMin),
    ("impossibleUntil".toList,
      .arr (d.impossibleUntil.val.map (fun t =>
        .obj [("id".toList, .str t.1), ("shortMin".toList, .num t.2.1),
          ("until".toList, .str (Field.renderDate t.2.2))]))),
    ("underusedLevels".toList, .arr (d.underusedLevels.val.map (fun t =>
      .obj [("id".toList, .str t.1), ("energy".toList, .num t.2.1.val), ("ci".toList, .num t.2.2.val)]))),
    ("blockedDeps".toList,
      .arr (d.blockedDeps.val.map (fun t =>
        .obj [("id".toList, .str t.1),
          ("deps".toList, .arr (t.2.map (fun x => .str (Field.renderDep x))))]))),
    ("unplaced".toList, .arr (d.unplaced.val.map (fun t => .obj [("id".toList, .str t.1), ("why".toList, .str (noPlaceName t.2))]))),
    ("served".toList, .arr (d.served.val.map (fun t =>
      .obj [("ix".toList, .num t.1), ("id".toList, .str t.2.1), ("ci".toList, .num t.2.2.val)])))]

/-- §7's answers, in `EmitWire.readPrio`'s own `{id, p}` shape. -/
def priosJson (c : Planner.Capped (Id × Fin 8)) : JVal :=
  .arr (c.val.map (fun p => .obj [("id".toList, .str p.1), ("p".toList, .num p.2.val)]))

/-- `state.last_plan_hash`'s sixteen lowercase hex digits, big-endian — the digits `Planner.mkHash?` reads
(`hashHex_of_zero_reads_back`), through `Json.hexChar`, which is this kernel's one hex writer. -/
def hashHex (h : Planner.PlanHash) : List Char :=
  (List.range Planner.hashHexLen).map
    (fun i => hexChar (h.val / 16 ^ (Planner.hashHexLen - 1 - i) % 16))

/-- **The day, as §10.2's seven keys.**  Every one is a projection of `Planner.dayPlan r` and nothing is recomputed. -/
def planJson (d : Planner.DayPlan) : List (List Char × JVal) :=
  [("day".toList, .str (Field.renderDate d.day)),
   ("window".toList, .obj [("lo".toList, .num d.window.1), ("hi".toList, .num d.window.2)]),
   ("budgetBlocks".toList, .num d.budgetBlocks),
   ("segments".toList, .arr (d.segments.map segJson)),
   ("diagnostics".toList, diagJson d.diagnostics),
   ("priorities".toList, priosJson d.priorities),
   ("hash".toList, .str (hashHex d.planHash))]

/-- **Into the `plan` object, beside `rows`.**  A `plan` key already written (by `EmitWire.withPlan`, the only writer of
it) gains these pairs; a response with no `plan` key yet gains one holding them.  The keys are disjoint, so neither
writer can overwrite the other. -/
def intoPlan : List (List Char × JVal) → List (List Char × JVal) → List (List Char × JVal)
  | [], xs => [("plan".toList, .obj xs)]
  | (k, v) :: rest, xs =>
    if k == "plan".toList then
      match v with
      | .obj ys => (k, .obj (ys ++ xs)) :: rest
      /- A `plan` key that is not an object: walked past, never overwritten.  `EmitWire.withPlan`
         is the only writer of that key and `jone` is always an object, so nothing reaches this. -/
      | _ => (k, v) :: intoPlan rest xs
    else (k, v) :: intoPlan rest xs

/-- The response's `ok` object, with the planner's keys in its `plan` object.  The shape guard is `EmitWire.withPlan`'s
own and is written ONCE, in `CapWire.intoOk`: a response that is not `{"ok": {…}}` is returned unchanged.  It was this
file's own copy of `CapWire.withLookahead`'s `match` until the W-28 repair step (AGENTS §5.3). -/
def withPlanner (r : JVal) (xs : List (List Char × JVal)) : JVal :=
  CapWire.intoOk r (fun kvs => intoPlan kvs xs)

/-! ## The request, assembled from what the call already decoded -/

/-- **D80's two refusals, by name, on the request the assembler built** (README gaps 3785, 3780 and 1984; parity P71
and P72): the day's evening inside the calendar (`Planner.PlanReq.eveningInsideTheCalendar`), then every candidate's
wire `ci` the plan's (`Planner.PlanReq.ciDisagreement` — the first that is not, named with both values); `none` when
the request pays both.  An `Option`, so check 9 can fold it to a constant (`Except … PlanReq` has no inhabitant). -/
def planReqRefusal (r : Planner.PlanReq) : Option PlannerRefusal :=
  if !r.eveningInsideTheCalendar then some PlannerRefusal.eveningPastTheCalendar
  else r.ciDisagreement.map (fun x => PlannerRefusal.ciDisagrees x.1 x.2.1 x.2.2)

/-- **`Planner.PlanReq`, from the values this call's own readers produced** — README gaps 1667-1669.  Gap **1668**:
`PlannerWit.mkPlanReq?` is a witness leaf (`mutate.py`'s `WITNESS_MODULES`), so the eight fields are decoded values
handed over, never decoded again (a second `loadPlan`, `Look.mkInput?` or `Seal.resumeRun` is gap 1325's defect).  It
obliges the **walls agreement** (gap 346, `wallsDisagree`), then D80's two (`planReqRefusal`) — BEFORE the routines (gap 4795). -/
def planReqOf (parts : CapParts) (bm : Nat) (q : PlannerIn) :
    Except PlannerRefusal Planner.PlanReq :=
  match parts.lg.bind LogAnswer.run with
  | none => .error PlannerRefusal.runAbsent
  | some run =>
    match Capped.ofList? (match parts.cands with | none => [] | some c => c.items) with
    | none => .error PlannerRefusal.candsPastCap
    | some cs =>
      if parts.cap.look.walls ≠
          Look.wallIndex parts.cap.look.tz parts.cap.look.day.cut.blockMin parts.plan.val then
        .error PlannerRefusal.wallsDisagree
      else
        let req : Planner.PlanReq := ⟨parts.plan, run, parts.cap.look, q.state, cs,
          ⟨parts.cap.bins, parts.cap.safety, parts.cap.dflt,
            (match parts.cands with | none => false | some c => c.hysteresis), bm⟩,
          Capped.nil, q.overrides⟩
        match planReqRefusal req with
        | some x => .error x
        | none =>
          match Planner.mkRoutines? parts.plan.val q.routines with
          | .error e => .error (PlannerRefusal.routineRefused e)
          | .ok rs => .ok { req with routines := rs }

/-- **D80 (a) of the capacity section's parts** (README gap 4793, the W-46 repair): `planReqRefusal` of the request
`planReqOf` builds with the section's parts aside.  The evening reads none of them (`Planner.PlanReq.eveningEnd`), and
with no candidate D80 (b) has nothing to disagree about, so this answers the evening alone; `none` without a replay. -/
def eveningFirst (parts : CapParts) : Option PlannerRefusal :=
  (parts.lg.bind LogAnswer.run).bind (fun run => planReqRefusal ⟨parts.plan, run, parts.cap.look, RuntimeIn.empty,
    Capped.nil, ⟨parts.cap.bins, parts.cap.safety, parts.cap.dflt, false, 0⟩, Capped.nil, none⟩)

/-! ## `overtime` — §9.1's "x extend +N block", answered by the kernel (W-34, README gap 2682)  R3 deletes
`planner::diff` and `planner::overtime_drops` with `tm-core/src/planner.rs`, and the TUI's overtime prompt
(`App::extend_drops`) is their one caller.  So the what-if crosses here: the request names an item and a count of
blocks, and the day's `plan` object gains `overtime` — `Planner.overtimeDiff`'s four fields, `removed` being fork
`overtime_drops`' answer.  The binary sends no `planner` section until R3 (README gap 2229), so this key is R3's to
send. -/

/-- **D58's `grown`** (W-36, README gap 2873): absent is none; present is the host's `remaining` and `plannedMin`, each
through `EmitWire.u32Within` and together through `Planner.mkGrown?`.  The host's `needMin` is NOT read — the day reads
no need but §7.3's, derived by its pass (gap 3004). -/
def readGrown (v : JVal) : Except PlannerRefusal (Option Planner.WfGrown) :=
  match EmitWire.optAtP v "grown" (PlannerRefusal.badOvertime PlanKey.grown) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some w) => do
    let r ← EmitWire.u32Within (PlannerRefusal.badOvertime PlanKey.remaining)
      (← EmitWire.natAtP w "remaining" (PlannerRefusal.badOvertime PlanKey.remaining))
    let m ← EmitWire.u32Within (PlannerRefusal.badOvertime PlanKey.plannedMin)
      (← EmitWire.natAtP w "plannedMin" (PlannerRefusal.badOvertime PlanKey.plannedMin))
    match Planner.mkGrown? ⟨r, m⟩ with
    | some g => pure (some g)
    | none => throw (PlannerRefusal.badOvertime PlanKey.grown)

/-- **`{"id": …, "blocks": …, "grown"?: …}`**, absent being no what-if — the id through `EmitWire.idWithin`, the count
through `EmitWire.u32Within` (fork `u32`), and D58's facts. -/
def readOvertime (sec : JVal) : Except PlannerRefusal (Option (Id × Nat × Option Planner.WfGrown)) :=
  match EmitWire.optAtP sec "overtime" (PlannerRefusal.badOvertime PlanKey.overtime) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some v) => do
    let idS ← EmitWire.strAtP v "id" (PlannerRefusal.badOvertime PlanKey.id)
    let id ← EmitWire.idWithin (PlannerRefusal.badOvertime PlanKey.id) idS
    let b ← EmitWire.u32Within (PlannerRefusal.badOvertime PlanKey.blocks)
      (← EmitWire.natAtP v "blocks" (PlannerRefusal.badOvertime PlanKey.blocks))
    pure (some (id, b, ← readGrown v))

/-- **`Planner.PlanDiff`, each field under its own name**: `removed` and `added` as id lists in the order `diff` holds
them, `moved` as `{id, from, to}` on the kernel's absolute seconds, and `driftMin`. -/
def diffJson (d : Planner.PlanDiff) : JVal :=
  .obj [("removed".toList, .arr (d.removed.map JVal.str)),
    ("added".toList, .arr (d.added.map JVal.str)),
    ("moved".toList, .arr (d.moved.map (fun m =>
      .obj [("id".toList, .str m.1), ("from".toList, .num m.2.1), ("to".toList, .num m.2.2)]))),
    ("driftMin".toList, .num d.driftMin)]

/-- **The what-if's answer, into the `plan` object** — nothing without an `overtime` key, and with one the whole of
`Planner.overtimeDiff` for that item and count, computed once. -/
def overtimeJson (r : Planner.PlanReq) : Option (Id × Nat × Option Planner.WfGrown) → List (List Char × JVal)
  | none => []
  | some (i, b, g) => [("overtime".toList, diffJson (Planner.overtimeDiff r i b g))]

/-- **The request, with its `planner` section.**  Without one this is `EmitWire.runRows`, byte for byte.  With one:
`runRows` answers first, so every refusal that stood before this step still comes first and in the same order; then the
section, then §16's `batchMaxMin`, then the request, then **the day** — `Planner.dayPlan`'s seven keys (compiled:
`Planner.dayPlanOnce`, W-42's `@[csimp]` twin), into the same `plan` object `rows` is in.  **A section refusal yields to
D80 (a)** (`eveningFirst`; README gap 4793): on a day whose evening runs past the calendar the reader may refuse a
routine window that evening carries past the calendar's last second, and the day is P71's, by P71's name.

**`now` is the capacity section's `at`, and is not read again** (README gap 1672, CLOSED).  W-27 called `CapWire.readAt`
a second time here and recorded that its refusal branch was unreachable because `runCap` had already accepted the same
key.  `Boundary.CapParts` hands the decoded value out instead: `parts.cap.look.today0.now` *is* what `readAt` produced
(`Section.today0` puts `s.atNow` there and `Look.mkInput?` carries it through), so the second call and its unreachable
branch are both gone rather than documented.

**`Planner.dayPlan` is total and stays total** (D28): there is no `dayPlan?` and no planner refusal family.  Every
refusal below is a refusal to *build the request* — a section the decoder rejects, a `batchMaxMin` past the fork's
`u32`, a missing capacity section, a missing replay, a wall index that is not this plan's, a window instance
`mkRoutine?` rejects.  Once a `PlanReq` exists the kernel answers, always. -/
def runPlanner (j : JVal) : Except JVal JVal :=
  match jget j "planner" with
  | .error e => .error (jsonErr e)
  | .ok none => EmitWire.runRows j
  | .ok (some sec) =>
    match EmitWire.runRowsP j with
    | .error e => .error e
    | .ok (_, none) => .error (plannerRefusalJson PlannerRefusal.capacityAbsent)
    | .ok (r, some parts) =>
      match readPlannerSection parts.cap.look.today0.now sec with
      | .error x => .error (plannerRefusalJson ((eveningFirst parts).getD x))
      | .ok q =>
        match readBatchMaxMin parts.sec with
        | .error x => .error (plannerRefusalJson x)
        | .ok bm =>
          match planReqOf parts bm q with
          | .error x => .error (plannerRefusalJson x)
          | .ok req =>
            match readOvertime sec with
            | .error x => .error (plannerRefusalJson x)
            | .ok ot => .ok (withPlanner r (planJson (Planner.dayPlan req) ++ overtimeJson req ot))

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

/-- **A readable `planner` section ANSWERS THE DAY.**

This replaces the two theorems W-27 proved on purpose so that the step building the response
would be the step deleting them (README gap 1667) — runPlanner_with_a_readable_section_answers
_as_runRows and its Rust twin a_readable_planner_section_changes_no_byte, both **deleted here**
and both written without backticks because neither exists any more.  Deleting them is not
weakening a law (D5): the old statement said the response *equals* `EmitWire.runRows`', this one
says it is that **with the day's seven keys added**, and the old statement is false of this
definition exactly because the kernel now answers. -/
theorem runPlanner_answers_the_day (j sec r : JVal) (b : Nat) (parts : CapParts)
    (q : PlannerIn) (req : Planner.PlanReq) (ot : Option (Id × Nat × Option Planner.WfGrown))
    (hp : jget j "planner" = .ok (some sec)) (hr : EmitWire.runRowsP j = .ok (r, some parts))
    (hs : readPlannerSection parts.cap.look.today0.now sec = .ok q)
    (hb : readBatchMaxMin parts.sec = .ok b) (hq : planReqOf parts b q = .ok req)
    (ho : readOvertime sec = .ok ot) :
    runPlanner j = .ok (withPlanner r (planJson (Planner.dayPlan req) ++ overtimeJson req ot)) := by
  simp only [runPlanner, hp, hr, hs, hb, hq, ho]

/-- **Without an `overtime` key the day is answered exactly as before W-34** — the seven keys
and nothing else.  This is `runPlanner_answers_the_day` as it stood until W-34, which is the
instance of the restated law at `ot = none`: W-34 added a key, so the old unconditional form is
false of a request carrying one (`overtimeJson_answers_the_what_if` is the one pair it adds). -/
theorem runPlanner_answers_the_day_without_an_overtime (j sec r : JVal) (b : Nat)
    (parts : CapParts) (q : PlannerIn) (req : Planner.PlanReq)
    (hp : jget j "planner" = .ok (some sec)) (hr : EmitWire.runRowsP j = .ok (r, some parts))
    (hs : readPlannerSection parts.cap.look.today0.now sec = .ok q)
    (hb : readBatchMaxMin parts.sec = .ok b) (hq : planReqOf parts b q = .ok req)
    (ho : readOvertime sec = .ok none) :
    runPlanner j = .ok (withPlanner r (planJson (Planner.dayPlan req))) := by
  rw [runPlanner_answers_the_day j sec r b parts q req none hp hr hs hb hq ho]
  simp [overtimeJson]

/-- **And an `overtime` key the decoder refuses refuses the call, by its own name.** -/
theorem runPlanner_refuses_an_overtime_the_decoder_refuses (j sec r : JVal) (b : Nat)
    (parts : CapParts) (q : PlannerIn) (req : Planner.PlanReq) (x : PlannerRefusal)
    (hp : jget j "planner" = .ok (some sec)) (hr : EmitWire.runRowsP j = .ok (r, some parts))
    (hs : readPlannerSection parts.cap.look.today0.now sec = .ok q)
    (hb : readBatchMaxMin parts.sec = .ok b) (hq : planReqOf parts b q = .ok req)
    (ho : readOvertime sec = .error x) :
    runPlanner j = .error (plannerRefusalJson x) := by
  simp only [runPlanner, hp, hr, hs, hb, hq, ho]

/-- **A refusal `EmitWire.runRowsP` makes reaches the host unchanged.**  Every law below
hypothesises `runRowsP j = .ok (…)`, so `runPlanner`'s own `| .error e => .error e` branch was
covered by NO law — only `tm/tests/kernel_planner_wire.rs` drove one instance of it (README gap
1882, the W-28 repair step).  D5 keeps relational laws proved rather than driven, and this is
the one that was missing: the wire adds nothing to a rows refusal and subtracts nothing from
it. -/
theorem runPlanner_passes_a_rows_refusal_through (j sec e : JVal)
    (hp : jget j "planner" = .ok (some sec)) (hr : EmitWire.runRowsP j = .error e) :
    runPlanner j = .error e := by
  simp only [runPlanner, hp, hr]

/-- **And a section that does not decode refuses the whole call, by its own name** — the sentence
that makes every bound in this module reachable from the FFI. -/
theorem runPlanner_refuses_a_section_the_decoder_refuses (j sec r : JVal) (parts : CapParts)
    (x : PlannerRefusal)
    (hp : jget j "planner" = .ok (some sec)) (hr : EmitWire.runRowsP j = .ok (r, some parts))
    (hs : readPlannerSection parts.cap.look.today0.now sec = .error x) (hg : eveningFirst parts = none) :
    runPlanner j = .error (plannerRefusalJson x) := by
  simp only [runPlanner, hp, hr, hs, hg, Option.getD]

/-- **A `planner` section without a `capacity` section is refused by name** — `PlanReq.look`
and `prio`'s five values are the capacity section's, so the request could not be assembled.
`Boundary.runCapP` answers `none` for the parts on exactly those requests. -/
theorem runPlanner_refuses_a_planner_section_without_a_capacity (j sec r : JVal)
    (hp : jget j "planner" = .ok (some sec)) (hr : EmitWire.runRowsP j = .ok (r, none)) :
    runPlanner j = .error (plannerRefusalJson PlannerRefusal.capacityAbsent) := by
  simp only [runPlanner, hp, hr]

/-- **And a `batchMaxMin` the decoder refuses refuses the call** — README gap 801's value with a
caller, which is what makes its bound more than a definition. -/
theorem runPlanner_refuses_a_batch_max_min_the_decoder_refuses (j sec r : JVal)
    (parts : CapParts) (q : PlannerIn) (x : PlannerRefusal)
    (hp : jget j "planner" = .ok (some sec)) (hr : EmitWire.runRowsP j = .ok (r, some parts))
    (hs : readPlannerSection parts.cap.look.today0.now sec = .ok q)
    (hb : readBatchMaxMin parts.sec = .error x) :
    runPlanner j = .error (plannerRefusalJson x) := by
  simp only [runPlanner, hp, hr, hs, hb]

/-- **A request the assembler cannot build is refused by name** — the seam's absent replay, a
wall index that is not the plan's (README gap 346), a candidate list past `Planner.maxCands`, a
window instance `mkRoutine?` rejects. -/
theorem runPlanner_refuses_a_request_the_assembler_refuses (j sec r : JVal) (b : Nat)
    (parts : CapParts) (q : PlannerIn) (x : PlannerRefusal)
    (hp : jget j "planner" = .ok (some sec)) (hr : EmitWire.runRowsP j = .ok (r, some parts))
    (hs : readPlannerSection parts.cap.look.today0.now sec = .ok q)
    (hb : readBatchMaxMin parts.sec = .ok b) (hq : planReqOf parts b q = .error x) :
    runPlanner j = .error (plannerRefusalJson x) := by
  simp only [runPlanner, hp, hr, hs, hb, hq]

/-! ### The response's laws -/

/-! ### The emitters, pinned

**`mutate.py` found ten of them pinned by NOTHING** — `routineErrName`, optNum, `optStr`,
pairJson, `flagsJson`, `noteJson`, `segJson`, `idsJson`, `diagJson` and `priosJson` each
survived `:= default` with a green `lake build TmKernel:static`, because every theorem above
is about the *shape* of `planJson` and none about the bytes any one emitter writes.  That is
W-27's finding one module along (five optional readers, three theorems) and these are the
theorems that answer it: each is a concrete witness, so a `default` in any of them moves a
value a `rfl` names. -/

/-- **Every field of a segment, at a value** — the eleven keys, in order, with `energy`, `item`,
`inst`, `planned`, `mult` and `note` all present, so `CapWire.optNatJson`, `optStr`,
`minutesJson`, `noteJson` and `flagsJson` are each pinned at a non-default by this one
sentence.  (Two of those names were this file's own optNum and pairJson until the W-28 repair
step deleted them as duplicates; §5.3's note above `optStr` says why.) -/
theorem segJson_writes_every_field_of_a_segment :
    segJson ⟨⟨0, 60, .block, some 3, some ['a'], some (['a'], ['b']),
        ⟨true, true, true, true, true, true, true⟩, some 25, some ⟨⟨3, 2⟩, by decide⟩,
        some (.noPosition ['a'] 30 100 200)⟩, by decide⟩
      = .obj [("start".toList, .num 0), ("stop".toList, .num 60),
          ("kind".toList, .str "block".toList), ("batch".toList, .arr []),
          ("energy".toList, .num 3), ("item".toList, .str ['a']),
          ("inst".toList, .obj [("id".toList, .str ['a']), ("inst".toList, .str ['b'])]),
          ("flags".toList, .obj [("done".toList, .bool true), ("current".toList, .bool true),
            ("underused".toList, .bool true), ("hot".toList, .bool true),
            ("mandatory".toList, .bool true), ("deferred".toList, .bool true),
            ("open".toList, .bool true)]),
          ("planned".toList, .num 25),
          ("mult".toList, .obj [("num".toList, .num 3), ("den".toList, .num 2)]),
          ("note".toList, .obj [("note".toList, .str "noPosition".toList),
            ("id".toList, .str ['a']), ("durMin".toList, .num 30), ("lo".toList, .num 100),
            ("hi".toList, .num 200)])] := rfl

/-- **And every absent field is `null`, never dropped and never defaulted** — a reader counts
the same eleven keys on every row. -/
theorem segJson_writes_null_for_every_absent_field :
    segJson ⟨⟨0, 0, .rest, none, none, none, {}, none, none, none⟩, by decide⟩
      = .obj [("start".toList, .num 0), ("stop".toList, .num 0),
          ("kind".toList, .str "rest".toList), ("batch".toList, .arr []),
          ("energy".toList, .null), ("item".toList, .null), ("inst".toList, .null),
          ("flags".toList, .obj [("done".toList, .bool false), ("current".toList, .bool false),
            ("underused".toList, .bool false), ("hot".toList, .bool false),
            ("mandatory".toList, .bool false), ("deferred".toList, .bool false),
            ("open".toList, .bool false)]),
          ("planned".toList, .null), ("mult".toList, .null), ("note".toList, .null)] := rfl

/-- **`Planner.Note`'s eleven constructors each spell their own name** (AGENTS §5.7), so a note
renamed here moves a key a host reads. -/
theorem noteJson_names_the_eleven :
    ([Planner.Note.travelDay, .noPosition ['a'] 1 2 3, .budgetSpent 1, .plannedOf 1 2,
      .bufferBefore ['a'], .travelDayWall, .paused, .interruption, .breakWhere ['x'],
      .idleAttributed ['x'], .runningLeft 5].map
        (fun n => match noteJson n with
          | .obj ((_, .str t) :: _) => t
          | _ => []))
      = [ "travelDay".toList, "noPosition".toList, "budgetSpent".toList, "plannedOf".toList,
          "bufferBefore".toList, "travelDayWall".toList, "paused".toList, "interruption".toList,
          "breakWhere".toList, "idleAttributed".toList, "runningLeft".toList] := rfl

/-- **§8.2 step 8's twelve fields, on a day with nothing wrong with it** — which is what
`Planner.dayPlan` answers today, so this is the object every response actually carries. -/
theorem diagJson_of_an_untroubled_day :
    diagJson Planner.Diagnostics.empty
      = .obj [("underused".toList, .arr []), ("aCapacityLost".toList, .num 0),
          ("hot".toList, .arr []), ("impossible".toList, .arr []),
          ("conflicts".toList, .arr []), ("blocked".toList, .arr []),
          ("deferred".toList, .arr []), ("waiting".toList, .arr []), ("notes".toList, .arr []),
          ("droppedTail".toList, .arr []),
          ("planHonesty".toList, .obj [("planned".toList, .num 0), ("total".toList, .num 0)]),
          ("restDebtMin".toList, .num 0), ("impossibleUntil".toList, .arr []),
          ("underusedLevels".toList, .arr []), ("blockedDeps".toList, .arr []), ("unplaced".toList, .arr []), ("served".toList, .arr [])] := rfl

/-- **And with something wrong with it**, so the list shapes and `idsJson` are pinned at a
value and not only at the empty list — the three whole tuples too since W-35: a date, two
levels and two deps, one of each spelling. -/
theorem diagJson_carries_its_lists :
    diagJson { Planner.Diagnostics.empty with
        hot := ⟨[['a']], by decide⟩,
        impossible := ⟨[(['b'], 30)], by decide⟩,
        conflicts := ⟨[(['c'], ['d'])], by decide⟩,
        notes := ⟨[.paused], by decide⟩,
        aCapacityLost := 7, restDebtMin := 12, planHonesty := (2, 5),
        impossibleUntil := ⟨[(['b'], 30, 739884)], by decide⟩,
        underusedLevels := ⟨[(['e'], 4, 2)], by decide⟩,
        blockedDeps := ⟨[(['f'], [.item ['g'], .event ['v']])], by decide⟩, unplaced := ⟨[(['h'], .noRunLeft), (['i'], .noSlotLeft), (['j'], .budgetSpent)], by decide⟩, served := ⟨[(3, ['h'], 2)], by decide⟩ }
      = .obj [("underused".toList, .arr []), ("aCapacityLost".toList, .num 7),
          ("hot".toList, .arr [.str ['a']]),
          ("impossible".toList,
            .arr [.obj [("id".toList, .str ['b']), ("shortMin".toList, .num 30)]]),
          ("conflicts".toList,
            .arr [.obj [("a".toList, .str ['c']), ("b".toList, .str ['d'])]]),
          ("blocked".toList, .arr []), ("deferred".toList, .arr []), ("waiting".toList, .arr []),
          ("notes".toList, .arr [.obj [("note".toList, .str "paused".toList)]]),
          ("droppedTail".toList, .arr []),
          ("planHonesty".toList, .obj [("planned".toList, .num 2), ("total".toList, .num 5)]),
          ("restDebtMin".toList, .num 12),
          ("impossibleUntil".toList,
            .arr [.obj [("id".toList, .str ['b']), ("shortMin".toList, .num 30),
              ("until".toList, .str (Field.renderDate 739884))]]),
          ("underusedLevels".toList,
            .arr [.obj [("id".toList, .str ['e']), ("energy".toList, .num 4),
              ("ci".toList, .num 2)]]),
          ("blockedDeps".toList,
            .arr [.obj [("id".toList, .str ['f']),
              ("deps".toList, .arr [.str ['^', 'g'], .str "event:v".toList])]]), ("unplaced".toList, .arr [.obj [("id".toList, .str ['h']), ("why".toList, .str "noRunLeft".toList)], .obj [("id".toList, .str ['i']), ("why".toList, .str "noSlotLeft".toList)], .obj [("id".toList, .str ['j']), ("why".toList, .str "budgetSpent".toList)]]), ("served".toList, .arr [.obj [("ix".toList, .num 3), ("id".toList, .str ['h']), ("ci".toList, .num 2)]])] := rfl

/-- **§7's answers go out in `EmitWire.readPrio`'s own `{id, p}` shape**, which is what lets a
host send back the day it was given. -/
theorem priosJson_is_the_id_and_the_priority :
    priosJson ⟨[(['a'], (3 : Fin 8)), (['b'], (0 : Fin 8))], by decide⟩
      = .arr [.obj [("id".toList, .str ['a']), ("p".toList, .num 3)],
              .obj [("id".toList, .str ['b']), ("p".toList, .num 0)]] := rfl

/-- **`Planner.RoutineErr`'s six names spell themselves, each with its id.** -/
theorem the_routine_errors_spell_themselves :
    (routineErrName (.unknownItem ['a']), routineErrName (.undeclaredWindow ['a']),
     routineErrName (.emptyWindow ['a']), routineErrName (.pastTheHorizon ['a']),
     routineErrName (.noMinutes ['a']), routineErrName .tooManyRoutines)
      = ("unknownItem a", "undeclaredWindow a", "emptyWindow a", "pastTheHorizon a",
         "noMinutes a", "tooManyRoutines") := rfl

/-! ### The emitters, pinned as FUNCTIONS and not at two points

**THE WITNESSES ABOVE ARE POINTS, AND A PERTURBATION THAT AGREES AT THEM IS INVISIBLE TO
LEAN** (the W-28 repair step, README gap 1881).  `mutate.py` asks one question — does anything
tell this body from a CONSTANT — and every theorem above answers it, which is what earned the
ten of them `PINNED`.  It is not the same question as "is this body the one the design says".
DRIVEN by an independent auditor in a clone: `segJson`'s `stop` written as
`.num (if s.val.stop ≤ 60 then s.val.stop else s.val.stop + 60)` agrees with BOTH witnesses
below — they use `stop = 60` and `stop = 0` — and `lake build TmKernel:static` was GREEN,
174 of 174 jobs; only `tm/tests/planner_invariants.rs` saw it, and named the two walls that
differed.  Two points cannot pin a function, and the answer is not a third point.

**SO EACH EMITTER GETS ONE LAW OVER ITS WHOLE DOMAIN.**  Each is `rfl`, each names every key
and every field in terms of the argument, and a body that differs from the one written here at
ANY input fails to elaborate — a value-dependent perturbation included.  The witnesses above
stay: they are what says the keys carry the values a READER expects at a value, and this says
the function is the function.  `planJson_of_a_planned_day_is_the_requests_own_views` below is
the same shape and was already written that way. -/

/-- **`segJson` is these eleven keys, for every segment.** -/
theorem segJson_is_its_eleven_keys (s : Planner.WfSeg) :
    segJson s
      = .obj [("start".toList, .num s.val.start), ("stop".toList, .num s.val.stop),
          ("kind".toList, .str (kindName s.val.kind)),
          ("batch".toList, .arr (batchOf s.val.kind)),
          ("energy".toList, CapWire.optNatJson (s.val.energy.map Fin.val)),
          ("item".toList, optStr s.val.item),
          ("inst".toList, match s.val.inst with
            | none => .null
            | some p => .obj [("id".toList, .str p.1), ("inst".toList, .str p.2)]),
          ("flags".toList, flagsJson s.val.flags),
          ("planned".toList, CapWire.optNatJson s.val.planned),
          ("mult".toList, minutesJson s.val.mult),
          ("note".toList, match s.val.note with | none => .null | some n => noteJson n)] := rfl

/-- **`flagsJson` is these seven marks, for every `SegFlags`.** -/
theorem flagsJson_is_its_seven_marks (f : Planner.SegFlags) :
    flagsJson f
      = .obj [("done".toList, .bool f.done), ("current".toList, .bool f.current),
          ("underused".toList, .bool f.underused), ("hot".toList, .bool f.hot),
          ("mandatory".toList, .bool f.mandatory), ("deferred".toList, .bool f.deferred),
          ("open".toList, .bool f.isOpen)] := rfl

/-- **`kindJson` is the name and the batch, for every kind.** -/
theorem kindJson_is_the_name_and_the_batch (k : Planner.SegKind) :
    kindJson k = .obj [("kind".toList, .str (kindName k)), ("batch".toList, .arr (batchOf k))] :=
  rfl

/-- **`idsJson` is the list, for every `IdList`.** -/
theorem idsJson_is_the_list (c : Planner.IdList) : idsJson c = .arr (c.val.map JVal.str) := rfl

/-- **`optStr` is `null` or the id, for every argument.** -/
theorem optStr_is_null_or_the_id (o : Option Id) :
    optStr o = match o with | none => .null | some i => .str i := rfl

/-- **`priosJson` is the `{id, p}` pairs, for every capped list.** -/
theorem priosJson_is_the_id_and_the_priority_of_every_pair (c : Planner.Capped (Id × Fin 8)) :
    priosJson c
      = .arr (c.val.map (fun p => .obj [("id".toList, .str p.1), ("p".toList, .num p.2.val)])) :=
  rfl

/-- **`diagJson` is these twelve fields, for every `Diagnostics`** — the fork's twelve, first and unchanged — **then the
three whole tuples W-35 added** (README gaps 2640 and 2743) and W-38's `unplaced` (D67) and `served` (gap 3343).  Re-proved with its statement
WIDENED by those keys (D5): the twelve entries are the ones this law always stated, byte for byte. -/
theorem diagJson_is_its_twelve_fields (d : Planner.Diagnostics) :
    diagJson d
      = .obj [("underused".toList, idsJson d.underused),
          ("aCapacityLost".toList, .num d.aCapacityLost),
          ("hot".toList, idsJson d.hot),
          ("impossible".toList,
            .arr (d.impossible.val.map (fun p =>
              .obj [("id".toList, .str p.1), ("shortMin".toList, .num p.2)]))),
          ("conflicts".toList,
            .arr (d.conflicts.val.map (fun p =>
              .obj [("a".toList, .str p.1), ("b".toList, .str p.2)]))),
          ("blocked".toList, idsJson d.blocked),
          ("deferred".toList, idsJson d.deferred),
          ("waiting".toList, idsJson d.waiting),
          ("notes".toList, .arr (d.notes.val.map noteJson)),
          ("droppedTail".toList, idsJson d.droppedTail),
          ("planHonesty".toList,
            .obj [("planned".toList, .num d.planHonesty.1),
              ("total".toList, .num d.planHonesty.2)]),
          ("restDebtMin".toList, .num d.restDebtMin),
          ("impossibleUntil".toList,
            .arr (d.impossibleUntil.val.map (fun t =>
              .obj [("id".toList, .str t.1), ("shortMin".toList, .num t.2.1),
                ("until".toList, .str (Field.renderDate t.2.2))]))),
          ("underusedLevels".toList,
            .arr (d.underusedLevels.val.map (fun t =>
              .obj [("id".toList, .str t.1), ("energy".toList, .num t.2.1.val),
                ("ci".toList, .num t.2.2.val)]))),
          ("blockedDeps".toList,
            .arr (d.blockedDeps.val.map (fun t =>
              .obj [("id".toList, .str t.1),
                ("deps".toList, .arr (t.2.map (fun x => .str (Field.renderDep x))))]))),
          ("unplaced".toList, .arr (d.unplaced.val.map (fun t => .obj [("id".toList, .str t.1), ("why".toList, .str (noPlaceName t.2))]))), ("served".toList, .arr (d.served.val.map (fun t => .obj [("ix".toList, .num t.1), ("id".toList, .str t.2.1), ("ci".toList, .num t.2.2.val)])))] := rfl

/-- **`noteJson` writes every FIELD of every constructor, and not only the name.**
`noteJson_names_the_eleven` pins the eleven names at eleven points; this pins the numbers and
the ids they carry, at every value they can take. -/
theorem noteJson_writes_every_field (id t : List Char) (durMin lo hi a b m : Nat) :
    (noteJson .travelDay, noteJson (.noPosition id durMin lo hi), noteJson (.budgetSpent a),
     noteJson (.plannedOf a b), noteJson (.bufferBefore id), noteJson .travelDayWall,
     noteJson .paused, noteJson .interruption, noteJson (.breakWhere t),
     noteJson (.idleAttributed t), noteJson (.runningLeft m))
      = (.obj [("note".toList, .str "travelDay".toList)],
         .obj [("note".toList, .str "noPosition".toList), ("id".toList, .str id),
           ("durMin".toList, .num durMin), ("lo".toList, .num lo), ("hi".toList, .num hi)],
         .obj [("note".toList, .str "budgetSpent".toList), ("blocksDone".toList, .num a)],
         .obj [("note".toList, .str "plannedOf".toList), ("planned".toList, .num a),
           ("total".toList, .num b)],
         .obj [("note".toList, .str "bufferBefore".toList), ("id".toList, .str id)],
         .obj [("note".toList, .str "travelDayWall".toList)],
         .obj [("note".toList, .str "paused".toList)],
         .obj [("note".toList, .str "interruption".toList)],
         .obj [("note".toList, .str "breakWhere".toList), ("text".toList, .str t)],
         .obj [("note".toList, .str "idleAttributed".toList), ("text".toList, .str t)],
         .obj [("note".toList, .str "runningLeft".toList), ("leftMin".toList, .num m)]) := rfl

/-- **`routineErrName` spells the name AND the id, for every id.** -/
theorem routineErrName_spells_every_id (id : Id) :
    (routineErrName (.unknownItem id), routineErrName (.undeclaredWindow id),
     routineErrName (.emptyWindow id), routineErrName (.pastTheHorizon id),
     routineErrName (.noMinutes id), routineErrName .tooManyRoutines)
      = (s!"unknownItem {String.ofList id}", s!"undeclaredWindow {String.ofList id}",
         s!"emptyWindow {String.ofList id}", s!"pastTheHorizon {String.ofList id}",
         s!"noMinutes {String.ofList id}", "tooManyRoutines") := rfl

/-- **The seven keys the day writes are design §10.2's, in its order.** -/
theorem planJson_writes_the_seven_keys (d : Planner.DayPlan) :
    (planJson d).map Prod.fst = planKeys := rfl

/-- **They are DISJOINT from the key `EmitWire.withPlan` already writes**, which is what lets one
`plan` object carry both a day the kernel planned and the rows a host asked it to render. -/
theorem the_plan_objects_keys_are_disjoint : planKeys.all (fun k => k ≠ "rows".toList) := by
  decide

/-- **Nothing in the response is recomputed**: every key is a view `Planner.PlanReq` already
had — the request's own day, the planner's window (`Planner.PlanReq.window`; gap 3341), §8.1's budget,
`dayRows`, `dayDiagnostics`, `dayPriorities` and the hash — and this is `rfl`. -/
theorem planJson_of_a_planned_day_is_the_requests_own_views (r : Planner.PlanReq) :
    planJson (Planner.dayPlan r)
      = [("day".toList, .str (Field.renderDate r.today)),
         ("window".toList, .obj [("lo".toList, .num r.window.1),
            ("hi".toList, .num r.window.2)]),
         ("budgetBlocks".toList, .num r.budgetBlocks),
         ("segments".toList, .arr ((Planner.dayRows r).map segJson)),
         ("diagnostics".toList, diagJson (Planner.dayDiagnostics r)),
         ("priorities".toList, priosJson (Planner.dayPriorities r)),
         ("hash".toList, .str (hashHex (Planner.planDigest r.tz ((Planner.dayRows r).map Subtype.val))))] := rfl

/-- **The day's rows and the emitted segments are the same list, of the same length.** -/
theorem planJson_segments_length (d : Planner.DayPlan) :
    (d.segments.map segJson).length = d.segments.length := by simp

/-- **`intoPlan` walks past every key that is not `plan`**, so the object it writes into is the
one `EmitWire.withPlan` wrote and never a new one beside it. -/
theorem intoPlan_skips_another_key (k : List Char) (v : JVal)
    (rest xs : List (List Char × JVal)) (h : (k == "plan".toList) = false) :
    intoPlan ((k, v) :: rest) xs = (k, v) :: intoPlan rest xs := by
  have hk : ¬ (k = "plan".toList) := by
    intro hc; rw [hc] at h; simp at h
  simp only [intoPlan]
  rw [h]
  simp

/-- **And appends into the `plan` object when it reaches one.** -/
theorem intoPlan_into_the_plan_object (ys xs rest : List (List Char × JVal)) :
    intoPlan (("plan".toList, .obj ys) :: rest) xs
      = ("plan".toList, .obj (ys ++ xs)) :: rest := by simp [intoPlan]

/-- **And makes one when there is none.** -/
theorem intoPlan_makes_a_plan_object (xs : List (List Char × JVal)) :
    intoPlan [] xs = [("plan".toList, .obj xs)] := rfl

/-- **The response's real shape, concretely**: a request that carried both sections gets one
`plan` object holding `rows` and then the day's seven keys — `EmitWire.withPlan`'s key first
because it was written first, and neither writer overwriting the other. -/
theorem withPlanner_shares_the_plan_object (docs report rows : JVal)
    (xs : List (List Char × JVal)) :
    withPlanner (.obj [("ok".toList, .obj [("docs".toList, docs), ("report".toList, report),
        ("plan".toList, .obj [("rows".toList, rows)])])]) xs
      = .obj [("ok".toList, .obj [("docs".toList, docs), ("report".toList, report),
          ("plan".toList, .obj (("rows".toList, rows) :: xs))])] := by
  simp [withPlanner, CapWire.intoOk, intoPlan]

/-- **And a request that carried only a `planner` section gets a `plan` object of its own.** -/
theorem withPlanner_makes_the_plan_object (docs report : JVal)
    (xs : List (List Char × JVal)) :
    withPlanner (.obj [("ok".toList, .obj [("docs".toList, docs), ("report".toList, report)])]) xs
      = .obj [("ok".toList, .obj [("docs".toList, docs), ("report".toList, report),
          ("plan".toList, .obj xs)])] := by
  simp [withPlanner, CapWire.intoOk, intoPlan]

/-- **The seam carries its run exactly when it carries its facts** (README gaps 1669 and 1783).

`Boundary.LogReq.seamFacts` and `seamRun` are guarded by the same `r.facts`, so a `LogAnswer`
cannot hold one without the other.  That is what makes `PlannerRefusal.runAbsent` a branch no
host reaches today: `CapWire.Section.today0` refuses `day0WithoutLog` when the facts are absent,
and it runs first — the ordering `tm/tests/kernel_planner_wire.rs` asserts rather than asserting
a refusal nothing can produce (AGENTS §9.2, the shape gap 1672 established). -/
theorem the_seam_carries_its_run_exactly_when_it_carries_its_facts (q : LogReq) (run : Seal.Run) :
    (q.seamFacts run).isSome = (q.seamRun run).isSome := by
  unfold LogReq.seamFacts LogReq.seamRun
  cases q.facts <;> rfl

/-- **…and the run it carries is the one it was given, exactly when facts were asked for** (W-35
track E, README gap 2849).  Written because re-verifying `LogReq.seamRun`'s check 9 row under the
second pass (README gap 2578) found the law above ALONE: with its proof sorried nothing told the
definition from `none`.  This is the definition's whole content, both directions. -/
theorem the_seam_carries_the_run_it_was_given_exactly_when_asked (q : LogReq) (run : Seal.Run) :
    q.seamRun run = some run ↔ q.facts = true := by
  unfold LogReq.seamRun
  cases q.facts <;> simp

/-- **`CapWire.maxCandidates` and `Planner.maxCands` are one number** — README gap **1330**'s
warning, stated for the first time.  It is `rfl`, so a diff that moves either has to move both or
fail here. -/
theorem the_two_candidate_caps_are_one_number :
    CapWire.maxCandidates = Planner.maxCands := rfl

/-- **The hash is sixteen digits**, which is the length `Planner.mkHash?` requires. -/
theorem hashHex_length (h : Planner.PlanHash) : (hashHex h).length = Planner.hashHexLen := by
  simp [hashHex]

/-- **And it reads back through the kernel's own reader** at zero — the value every day carried
until W-34's emitter; `hashHex_reads_back` is the law at every digest, this is its oldest case. -/
theorem hashHex_of_zero_reads_back :
    Planner.mkHash? (hashHex Planner.PlanHash.zero) = some Planner.PlanHash.zero := by decide

/-- **`EmitWire.readKind` reads back every kind `kindName` writes** — the eleven names are one
table, not two, so a kind renamed on one side fails here rather than on a host. -/
theorem readKind_reads_back_every_kind_it_writes (i : Nat) :
    EmitWire.readKind i (kindJson .block) = .ok .block ∧
    EmitWire.readKind i (kindJson .brk) = .ok .brk ∧
    EmitWire.readKind i (kindJson .routine) = .ok .routine ∧
    EmitWire.readKind i (kindJson .wall) = .ok .wall ∧
    EmitWire.readKind i (kindJson .rest) = .ok .rest ∧
    EmitWire.readKind i (kindJson .optional) = .ok .optional ∧
    EmitWire.readKind i (kindJson .windDown) = .ok .windDown ∧
    EmitWire.readKind i (kindJson .sleep) = .ok .sleep ∧
    EmitWire.readKind i (kindJson .lost) = .ok .lost ∧
    EmitWire.readKind i (kindJson .ghost) = .ok .ghost ∧
    EmitWire.readKind i (kindJson (.batch ⟨[['a'], ['b']], by decide⟩))
      = .ok (.batch ⟨[['a'], ['b']], by decide⟩) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The export is `callPlanner`.** -/
theorem callExport_is_callPlanner (input : String) : callExport input = callPlanner input := rfl

/-! ### The digest's sixteen digits read back (W-34 track H)

`Planner.dayPlan` carries `Planner.planDigest` since W-34, so the value `hashHex` writes is no
longer the constant zero `hashHex_of_zero_reads_back` was about.  The law below is at EVERY
digest: `Planner.mkHash?` — the one hex reader, `state.lastHash`'s decoder on this very wire —
reads back exactly the `PlanHash` `hashHex` wrote.  So the value a host stores from `plan.hash`
and hands back as `state.lastHash` reads back as it was stored (not "the value the kernel
compares": nothing here compares it, the host does — W-34 repair, README gap 2734). -/

/-- The big-endian base-16 fold `Planner.mkHash?` runs, over the digits `hashHex` writes, is the
number: `n` digits of `h < 16^n` fold back to `h`. -/
theorem hexFold_digits : ∀ (n h : Nat), h < 16 ^ n →
    ((List.range n).map (fun i => h / 16 ^ (n - 1 - i) % 16)).foldl (fun a d => a * 16 + d) 0 = h
  | 0, h, hh => by simp at hh; simp [hh]
  | n + 1, h, hh => by
    rw [List.range_succ, List.map_append, List.foldl_append]
    have hq : h / 16 < 16 ^ n := by
      rw [Nat.pow_succ] at hh; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hh)
    have hmap : (List.range n).map (fun i => h / 16 ^ (n + 1 - 1 - i) % 16)
        = (List.range n).map (fun i => h / 16 / 16 ^ (n - 1 - i) % 16) := by
      apply List.map_congr_left
      intro i hi
      have hin : i < n := List.mem_range.1 hi
      have he : n + 1 - 1 - i = (n - 1 - i) + 1 := by omega
      rw [he, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
    rw [hmap, hexFold_digits n (h / 16) hq]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
      Nat.add_sub_cancel, Nat.sub_self, Nat.pow_zero, Nat.div_one]
    omega

/-- **Every digest `hashHex` writes, `Planner.mkHash?` reads back** — the round trip at every
`PlanHash`, not only at zero. -/
theorem hashHex_reads_back (h : Planner.PlanHash) : Planner.mkHash? (hashHex h) = some h := by
  obtain ⟨v, hv⟩ := h
  have hlen : (hashHex ⟨v, hv⟩).length = Planner.hashHexLen := hashHex_length _
  have hdig : ∀ i ∈ List.range Planner.hashHexLen,
      hexDigit (hexChar (v / 16 ^ (Planner.hashHexLen - 1 - i) % 16))
        = some (v / 16 ^ (Planner.hashHexLen - 1 - i) % 16) :=
    fun i _ => hexDigit_hexChar _ (Nat.mod_lt _ (by decide))
  have hfold : ∀ (l : List Nat) (a : Nat), (∀ d ∈ l, d < 16) →
      (l.map hexChar).foldl
          (fun acc c => acc.bind (fun n => (hexDigit c).map (fun d => n * 16 + d))) (some a)
        = some (l.foldl (fun a d => a * 16 + d) a) := by
    intro l
    induction l with
    | nil => intro a _; rfl
    | cons d ds ih =>
      intro a hl
      simp only [List.map_cons, List.foldl_cons]
      rw [show (some a).bind (fun n => (hexDigit (hexChar d)).map (fun x => n * 16 + x))
          = some (a * 16 + d) by
        rw [hexDigit_hexChar d (hl d (List.mem_cons_self))]; rfl]
      exact ih (a * 16 + d) (fun x hx => hl x (List.mem_cons_of_mem d hx))
  have hbound : v < 16 ^ Planner.hashHexLen := by
    have : Planner.hashBound = 16 ^ Planner.hashHexLen := by decide
    rw [← this]; exact hv
  unfold Planner.mkHash?
  rw [if_neg (by rw [hlen]; exact fun h => h rfl)]
  have hmapc : hashHex ⟨v, hv⟩ = ((List.range Planner.hashHexLen).map
      (fun i => v / 16 ^ (Planner.hashHexLen - 1 - i) % 16)).map hexChar := by
    simp [hashHex, List.map_map]
  rw [hmapc, hfold _ 0 (by
      intro d hd
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hd
      exact Nat.mod_lt _ (by decide)),
    hexFold_digits Planner.hashHexLen v hbound]
  simp only [hv, dif_pos]


/-! ## W-34: the `overtime` key's laws, and the twelfth note

APPENDED 2026-09-26 (stage 6, run W-34, track D; README gaps 2680-2682).  `readOvertime`,
`diffJson` and `overtimeJson` are the `planner` section's what-if (§9.1's "x extend +N block"),
and `Planner.Note.soFar` is fork `open_block_segment`'s note, on the wire as `soFar`. -/

/-- **No `overtime` key is no what-if.** -/
theorem readOvertime_of_an_absent_key : readOvertime (.obj []) = .ok none := rfl

/-- **One item and one block, read.** -/
theorem readOvertime_accepts_an_extension :
    readOvertime (.obj [("overtime".toList, .obj [("id".toList, .str "m1".toList),
      ("blocks".toList, .num 1)])]) = .ok (some (['m','1'], 1, none)) := by rfl

/-- **A count past the fork's `u32` is refused by name** (R10), through `EmitWire.u32Within`. -/
theorem readOvertime_refuses_blocks_past_the_width :
    readOvertime (.obj [("overtime".toList, .obj [("id".toList, .str "m1".toList),
      ("blocks".toList, .num 4294967296)])])
      = .error (PlannerRefusal.badOvertime PlanKey.blocks) := by rfl

/-- **A what-if with no item is refused by name**, never read as "extend nothing". -/
theorem readOvertime_refuses_a_missing_id :
    readOvertime (.obj [("overtime".toList, .obj [("blocks".toList, .num 1)])])
      = .error (PlannerRefusal.badOvertime PlanKey.id) := by rfl

/-- **An id past the bound is refused**, through `EmitWire.idWithin`, at every id — stated over
whatever the section's two lookups return, so it is a fact about the decoder and not about one
JSON object (the shape of `readOverrides_refuses_a_long_drop_id`). -/
theorem readOvertime_refuses_a_long_id (sec v : JVal) (s : List Char)
    (hv : EmitWire.optAtP sec "overtime" (PlannerRefusal.badOvertime PlanKey.overtime)
      = .ok (some v))
    (hs : EmitWire.strAtP v "id" (PlannerRefusal.badOvertime PlanKey.id) = .ok s)
    (h : CapWire.maxCandId < s.length) :
    readOvertime sec = .error (PlannerRefusal.badOvertime PlanKey.id) := by
  simp only [readOvertime, hv, hs, bind, Except.bind,
    EmitWire.idWithin_refuses_a_long_id (PlannerRefusal.badOvertime PlanKey.id) s h]

/-- **The refusal spells itself.** -/
theorem the_overtime_refusal_spells_itself :
    (PlannerRefusal.badOvertime PlanKey.blocks).text = "badOvertime blocks" ∧
      (PlannerRefusal.badOvertime PlanKey.id).text = "badOvertime id" := ⟨rfl, rfl⟩

/-- **Without an `overtime` key the `plan` object gains nothing.** -/
theorem overtimeJson_of_none (r : Planner.PlanReq) : overtimeJson r none = [] := rfl

/-- **With one it gains exactly `overtime`, and it is `Planner.overtimeDiff`'s whole answer.** -/
theorem overtimeJson_answers_the_what_if (r : Planner.PlanReq) (i : Id) (b : Nat) (g : Option Planner.WfGrown) :
    overtimeJson r (some (i, b, g)) =
      [("overtime".toList, diffJson (Planner.overtimeDiff r i b g))] := rfl

/-- **`diffJson` writes every field of a `PlanDiff`**, at every value, under its own key. -/
theorem diffJson_writes_every_field (d : Planner.PlanDiff) :
    diffJson d = .obj [("removed".toList, .arr (d.removed.map JVal.str)),
      ("added".toList, .arr (d.added.map JVal.str)),
      ("moved".toList, .arr (d.moved.map (fun m =>
        .obj [("id".toList, .str m.1), ("from".toList, .num m.2.1), ("to".toList, .num m.2.2)]))),
      ("driftMin".toList, .num d.driftMin)] := rfl

/-- **The `removed` key IS fork `overtime_drops`' answer** — the ids the extended day no longer
holds, from `Planner.overtimeDiff` and nowhere else. -/
theorem the_overtime_keys_removed_is_overtime_drops (r : Planner.PlanReq) (i : Id) (b : Nat) (g : Option Planner.WfGrown) :
    overtimeJson r (some (i, b, g)) =
      [("overtime".toList, .obj [("removed".toList,
          .arr ((Planner.overtimeDiff r i b g).removed.map JVal.str)),
        ("added".toList, .arr ((Planner.overtimeDiff r i b g).added.map JVal.str)),
        ("moved".toList, .arr ((Planner.overtimeDiff r i b g).moved.map (fun m =>
          .obj [("id".toList, .str m.1), ("from".toList, .num m.2.1),
            ("to".toList, .num m.2.2)]))),
        ("driftMin".toList, .num (Planner.overtimeDiff r i b g).driftMin)])] := rfl

/-- **The twelfth note, `soFar`** — fork `open_block_segment`'s `"<n>m so far"`, the name and the
minutes; `noteJson_names_the_eleven` and `noteJson_writes_every_field` pin the other eleven. -/
theorem noteJson_writes_so_far (m : Nat) :
    noteJson (.soFar m) =
      .obj [("note".toList, .str "soFar".toList), ("workedMin".toList, .num m)] := rfl

/-- **The running break's word is the one the request carried** (W-35, D57 (1), parity P45):
`Planner.BreakPlace.word` is `placeOf?`'s inverse on all four places, so the note on the
running break's row (`Planner.breakRows`) spells the `place` the host sent, byte for byte. -/
theorem placeOf_reads_the_word (p : BreakPlace) : placeOf? p.word = some p := by
  cases p <;> decide

/-- **A batch row's members are its ids, in order, and every other kind has none** (W-35 track E,
README gap 2849).  Re-verifying `batchOf`'s check 9 row under the second pass found
`readKind_reads_back_every_kind_it_writes` ALONE: a law at every row index, whose proof, sorried,
left nothing that told the definition from `[]`.  This is the definition at two kinds, computed. -/
theorem batchOf_is_the_batchs_ids :
    batchOf (.batch ⟨[['a'], ['b']], by decide⟩) = [.str ['a'], .str ['b']] ∧
    batchOf .block = [] := by
  decide

/-- **`respondPlanner` answers a request's bytes** (W-35 track E, README gap 2849).  Re-verifying
`respondPlanner`'s check 9 row under the second pass found
`callPlanner_without_a_planner_section_is_callRows` ALONE: a law under two hypotheses, whose proof,
sorried, left nothing that told the definition from a constant.  This is the definition at one
request, `{"docs":[]}`, computed: an `ok` answer. -/
theorem respondPlanner_answers_an_empty_request :
    (match respondPlanner ['{', '"', 'd', 'o', 'c', 's', '"', ':', '[', ']', '}'] with
     | .obj ((k, _) :: _) => k == ['o', 'k']
     | _ => false) = true := by
  decide

/-- **What the FFI runs is `respondPlanner`'s answer, emitted** (W-35 track E, README gap 2849).
Re-verifying `callPlanner`'s check 9 row under the second pass found
`callPlanner_without_a_planner_section_is_callRows` ALONE, at both of its constants.  This is the
definition's body restated, and it is the WEAKEST pin there is, chosen on a measurement: a value-level
witness — the bytes `callPlanner` answers for the 11-byte request `{"docs":[]}` — was killed at the
8 GB cap in 7 s (a `String` round trip through the kernel; AGENTS §5.10a's class), so the value is
pinned one level down, at `respondPlanner_answers_an_empty_request`, and this joins the two. -/
theorem callPlanner_is_the_emitted_answer (input : String) :
    callPlanner input = String.ofList (jemit (respondPlanner input.toList)) := rfl
/-! ## W-36 (track K): D58's `grown`, read (README gap 2873)

APPENDED 2026-09-27.  `readGrown` is the `overtime` object's third key: the host's grown facts, the
kernel's what-if plans the grown request (`Planner.overtimeDiff`'s `g`), and the host's `needMin`
is not read (README gap 3004). -/

/-- **An absent `grown` is none**: the what-if is the estimate's, as before W-36. -/
theorem readGrown_of_an_absent_key : readGrown (.obj []) = .ok none := rfl

/-- **The host's two numbers, read.** -/
theorem readGrown_accepts_the_hosts_facts :
    (readGrown (.obj [("grown".toList, .obj [("remaining".toList, .num 150),
      ("plannedMin".toList, .num 180), ("needMin".toList, .num 195)])])).map
        (Option.map Subtype.val) = .ok (some ⟨150, 180⟩) := by rfl

/-- **A remaining past the fork's `u32` is refused by name** (R10), through `EmitWire.u32Within`. -/
theorem readGrown_refuses_a_remaining_past_the_width :
    readGrown (.obj [("grown".toList, .obj [("remaining".toList, .num 4294967296),
      ("plannedMin".toList, .num 1)])]) = .error (PlannerRefusal.badOvertime PlanKey.remaining) := by
  rfl

/-- **Planned minutes past the width are refused by name.** -/
theorem readGrown_refuses_planned_minutes_past_the_width :
    readGrown (.obj [("grown".toList, .obj [("remaining".toList, .num 1),
      ("plannedMin".toList, .num 4294967296)])]) = .error (PlannerRefusal.badOvertime PlanKey.plannedMin) := by
  rfl

/-- **A `grown` that is not an object is refused by name**, never read as none — by the first key
it cannot find, as `readOvertime` refuses an `overtime` that is not an object by its `id`. -/
theorem readGrown_refuses_a_grown_that_is_not_an_object :
    readGrown (.obj [("grown".toList, .num 1)]) = .error (PlannerRefusal.badOvertime PlanKey.remaining) := by
  rfl

/-- **The what-if carries the facts it was sent** — `readOvertime` hands `readGrown`'s answer to
`Planner.overtimeDiff` whole. -/
theorem readOvertime_carries_the_grown_facts :
    (readOvertime (.obj [("overtime".toList, .obj [("id".toList, .str "m1".toList),
      ("blocks".toList, .num 1), ("grown".toList, .obj [("remaining".toList, .num 150),
      ("plannedMin".toList, .num 180)])])])).map (Option.map (fun t => (t.1, t.2.1, t.2.2.map Subtype.val)))
      = .ok (some (['m','1'], 1, some ⟨150, 180⟩)) := by rfl

/-- **The refusals spell themselves.** -/
theorem the_grown_refusals_spell_themselves :
    (PlannerRefusal.badOvertime PlanKey.grown).text = "badOvertime grown" ∧
      (PlannerRefusal.badOvertime PlanKey.remaining).text = "badOvertime remaining" := ⟨rfl, rfl⟩

/-- **A `grown` carried twice is refused `badOvertime grown`** — the one input that reaches that
name, because `Planner.mkGrown?`'s own refusal cannot fire behind the two width reads
(`mkGrown?_accepts_what_the_width_reads_pass`). -/
theorem readGrown_refuses_a_grown_carried_twice :
    readGrown (.obj [("grown".toList, .obj []), ("grown".toList, .obj [])])
      = .error (PlannerRefusal.badOvertime PlanKey.grown) := by rfl

/-- **The smart constructor accepts whatever the two width reads pass**: `EmitWire.u32Within`'s bound,
`CapWire.maxRemaining`, IS `Look.maxPlanMinutes`, the width `Planner.GrownFacts.wf` checks — so the
constructor is used (R10) and its refusal is a second statement of one bound, said here rather
than left to look like a check an input could fail. -/
theorem mkGrown?_accepts_what_the_width_reads_pass (r m : Nat) (hr : r ≤ CapWire.maxRemaining)
    (hm : m ≤ CapWire.maxRemaining) : (Planner.mkGrown? ⟨r, m⟩).isSome = true := by
  have hw : Planner.GrownFacts.wf ⟨r, m⟩ = true := by
    simp only [Planner.GrownFacts.wf, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hr, hm⟩
  unfold Planner.mkGrown?
  rw [dif_pos hw]
  rfl


/-! ## W-36 track T: `state.active.workedMin`, the host's worked minutes (README gap 2920, P55)

The planner's ONE reading of the running block's worked minutes is the host's —
`Replay::active_worked_min`, what `tm now` prints and `tm done` logs — and it crosses here, in the
active record where the host holds it, into `RuntimeIn.worked` through `Planner.workedOf?` (the host's
width since W-41, `Look.maxPlanMinutes` reused).  **Optional on the wire**: a record without it reads `none`,
and the planner then falls back to the log's own reading (fork `active_run`'s), so every request
the proptest arms built before W-36 means what it meant.  `tm_core::planwire::add_worked_min` is
the one host encoder of the key.  `readOptWorked` reads it last, so an active record the other
readers refuse is refused by their names first. -/

/-- **The key is read as itself — past a day too, since W-41; absent it reads `none`; past the host's width it is
refused** by the active record's name, never clamped (R10). -/
theorem readState_reads_the_hosts_worked_minutes :
    (readState ⟨1000, 0⟩ (.obj [("active".toList, .obj [("id".toList, .str "m2".toList),
        ("started".toList, .num 900), ("estMin".toList, .num 60),
        ("workedMin".toList, .num 1441)])])).map (fun st => st.worked.map Fin.val) = .ok (some 1441) ∧
    (readState ⟨1000, 0⟩ (.obj [("active".toList, .obj [("id".toList, .str "m2".toList),
        ("started".toList, .num 900), ("estMin".toList, .num 60)])])).map
        (fun st => st.worked.map Fin.val) = .ok none ∧
    (readState ⟨1000, 0⟩ (.obj [("active".toList, .obj [("id".toList, .str "m2".toList),
        ("started".toList, .num 900), ("estMin".toList, .num 60),
        ("workedMin".toList, .num 4294967296)])])).map (fun st => st.worked.map Fin.val)
      = .error (PlannerRefusal.badActive PlanKey.workedMin) :=
  ⟨rfl, rfl, rfl⟩

/-- **R10's rejection theorem, general**: whatever the record, a `workedMin` past the host's width is the
active record's refusal. -/
theorem readOptWorked_refuses_a_reading_past_the_width (sec a : JVal) (n : Nat)
    (ha : EmitWire.optAtP sec "active" (PlannerRefusal.badState PlanKey.active) = .ok (some a))
    (hn : EmitWire.optNatAtP a "workedMin" (PlannerRefusal.badActive PlanKey.workedMin)
      = .ok (some n))
    (h : Look.maxPlanMinutes < n) :
    readOptWorked sec = .error (PlannerRefusal.badActive PlanKey.workedMin) := by
  unfold readOptWorked
  rw [ha]
  simp only
  rw [hn]
  simp only [Planner.a_worked_reading_past_the_width_is_refused n h]

/-- **The key's name spells itself** — a refusal a host reads by text. -/
theorem planKey_workedMin_is_the_wire_key : PlanKey.workedMin.name = "workedMin" := rfl

/-- **The capacity answer's `until` is `Planner.answerUntil`'s** (W-36 repair, README gap 3137):
`CapWire.grantJsonF` writes a floor answer's last day and `CapWire.grantJson` a grant's due date
under `until`, by the same rule `Planner.answerUntil` — "the date's one reader" — states, and this
ties the two spellings so a change to either shows up as a broken proof, not as a wire the host
reads one way and D60's key another. -/
theorem the_wire_until_is_answerUntil (o : Look.FloorOut) :
    (match CapWire.grantJsonF o with | .obj kv => kv.lookup "until".toList | _ => none) =
      some (match Planner.answerUntil o with
        | some d => JVal.str (Field.renderDate d)
        | none => JVal.null) := by
  rcases o with ⟨out, floor⟩
  cases floor with
  | some g => simp [CapWire.grantJsonF, Planner.answerUntil, List.lookup]
  | none =>
    cases hg : out.grant with
    | some g => simp [CapWire.grantJsonF, CapWire.grantJson, Planner.answerUntil, List.lookup, hg]
    | none => simp [CapWire.grantJsonF, CapWire.grantJson, Planner.answerUntil, List.lookup, hg]

/-! ## §8.2 step 8's pair and id keys are their tuples' projections, ON THE WIRE (stage 6 W-38, track R; README gap 3282)

APPENDED 2026-09-29 (stage 6, run W-38, track R).  `planner_invariants`' step-8 arm
(`the_kernel_writes_the_rest_of_step_8_as_the_fork_does`) asks, of the kernel's own `diagnostics` object on every
generated day, that `impossible` be `impossibleUntil`'s `(id, shortMin)`, `underused` be `underusedLevels`' ids and
`blocked` be `blockedDeps`' ids — the three comparisons that arm makes of the kernel against ITSELF — and R3 deletes
the arm with the fork region it sits in.  Read by the arms: no other arm of the region compares two keys of the
kernel's own answer; every other comparison there is the kernel against the fork.  So these are the three as kernel
laws, at the JSON the export writes (`jget` over `diagJson (dayPlan r).diagnostics`, the value `planJson` puts under
`diagnostics`), and nothing is lost with the arm: each pair of keys renders ONE list — the tuple key every entry
whole, the pair or id key its projection — entry for entry and in order, which is stronger than the arm's multiset
comparison and needs no generated day to hold. -/

/-- **`impossible` is `impossibleUntil`'s `(id, shortMin)`, on the wire.** -/
theorem the_impossible_key_is_the_impossibleUntil_key_projected (r : Planner.PlanReq) :
    jget (diagJson (Planner.dayPlan r).diagnostics) "impossibleUntil"
      = .ok (some (.arr ((Planner.dayPlan r).diagnostics.impossibleUntil.val.map (fun t =>
          .obj [("id".toList, .str t.1), ("shortMin".toList, .num t.2.1),
            ("until".toList, .str (Field.renderDate t.2.2))])))) ∧
    jget (diagJson (Planner.dayPlan r).diagnostics) "impossible"
      = .ok (some (.arr ((Planner.dayPlan r).diagnostics.impossibleUntil.val.map (fun t =>
          .obj [("id".toList, .str t.1), ("shortMin".toList, .num t.2.1)])))) := by
  have hp := Planner.dayDiagnostics_impossible_is_the_projection r
  refine ⟨rfl, ?_⟩
  show jget (diagJson (Planner.dayDiagnostics r)) "impossible" = _
  have hj : jget (diagJson (Planner.dayDiagnostics r)) "impossible"
      = .ok (some (.arr ((Planner.dayDiagnostics r).impossible.val.map (fun p =>
          .obj [("id".toList, .str p.1), ("shortMin".toList, .num p.2)])))) := rfl
  rw [hj, ← hp, List.map_map]
  rfl

/-- **`underused` is `underusedLevels`' ids, on the wire.** -/
theorem the_underused_key_is_the_underusedLevels_key_projected (r : Planner.PlanReq) :
    jget (diagJson (Planner.dayPlan r).diagnostics) "underusedLevels"
      = .ok (some (.arr ((Planner.dayPlan r).diagnostics.underusedLevels.val.map (fun t =>
          .obj [("id".toList, .str t.1), ("energy".toList, .num t.2.1.val),
            ("ci".toList, .num t.2.2.val)])))) ∧
    jget (diagJson (Planner.dayPlan r).diagnostics) "underused"
      = .ok (some (.arr ((Planner.dayPlan r).diagnostics.underusedLevels.val.map (fun t =>
          .str t.1)))) := by
  have hp := Planner.dayDiagnostics_underused_is_the_projection r
  refine ⟨rfl, ?_⟩
  show jget (diagJson (Planner.dayDiagnostics r)) "underused" = _
  have hj : jget (diagJson (Planner.dayDiagnostics r)) "underused"
      = .ok (some (.arr ((Planner.dayDiagnostics r).underused.val.map JVal.str))) := rfl
  rw [hj, ← hp, List.map_map]
  rfl

/-- **`blocked` is `blockedDeps`' ids, on the wire.** -/
theorem the_blocked_key_is_the_blockedDeps_key_projected (r : Planner.PlanReq) :
    jget (diagJson (Planner.dayPlan r).diagnostics) "blockedDeps"
      = .ok (some (.arr ((Planner.dayPlan r).diagnostics.blockedDeps.val.map (fun t =>
          .obj [("id".toList, .str t.1),
            ("deps".toList, .arr (t.2.map (fun x => .str (Field.renderDep x))))])))) ∧
    jget (diagJson (Planner.dayPlan r).diagnostics) "blocked"
      = .ok (some (.arr ((Planner.dayPlan r).diagnostics.blockedDeps.val.map (fun t =>
          .str t.1)))) := by
  have hp := Planner.dayDiagnostics_blocked_is_the_projection r
  refine ⟨rfl, ?_⟩
  show jget (diagJson (Planner.dayDiagnostics r)) "blocked" = _
  have hj : jget (diagJson (Planner.dayDiagnostics r)) "blocked"
      = .ok (some (.arr ((Planner.dayDiagnostics r).blocked.val.map JVal.str))) := rfl
  rw [hj, ← hp, List.map_map]
  rfl

/-- **`served` is step 5's walk order, on the wire** (W-38, README gap 3343): one `{ix, id, ci}` object per ranked
answer, in `rankedLe`'s order — the list a harness reads instead of a Rust copy of the kernel's order. -/
theorem the_served_key_is_the_walks_order (r : Planner.PlanReq) :
    jget (diagJson (Planner.dayPlan r).diagnostics) "served"
      = .ok (some (.arr (r.rankedCands.map (fun x =>
          .obj [("ix".toList, .num x.key.ix), ("id".toList, .str x.out.out.cand.id),
            ("ci".toList, .num x.out.out.cand.ci.val)])))) := by
  have hj : jget (diagJson (Planner.dayDiagnostics r)) "served"
      = .ok (some (.arr ((Planner.dayDiagnostics r).served.val.map (fun t =>
          .obj [("ix".toList, .num t.1), ("id".toList, .str t.2.1), ("ci".toList, .num t.2.2.val)])))) := rfl
  show jget (diagJson (Planner.dayDiagnostics r)) "served" = _
  rw [hj, Planner.dayDiagnostics_served, Planner.PlanReq.dayServed, List.map_map]
  rfl

/-! ## W-41 (track K): D80's two refusals, by name (README gaps 3785, 3780 and 1984; parity P71, P72)

`planReqRefusal` is where the assembled request meets the two clauses `Planner.lean` defines on it — one definition of
each, read by this decoder and by the wind-down law alike.  The day's evening first (a day past the calendar has no row
to argue about), then the candidates, the first disagreeing one named with the wire's value and the plan's. -/

/-- **D80 (a): a day whose evening runs past the calendar's last second is refused by name.** -/
theorem planReqRefusal_names_an_evening_past_the_calendar (r : Planner.PlanReq)
    (h : r.eveningInsideTheCalendar = false) :
    planReqRefusal r = some PlannerRefusal.eveningPastTheCalendar := by
  unfold planReqRefusal; rw [h]; rfl

/-- **D80 (b): a candidate whose wire `ci` is not the plan's is refused, named with both values** — on a day whose
evening the clause above accepts. -/
theorem planReqRefusal_names_a_candidate_whose_ci_disagrees (r : Planner.PlanReq)
    (hev : r.eveningInsideTheCalendar = true) (i : Id) (w : Fin 6) (p : Option (Fin 6))
    (h : r.ciDisagreement = some (i, w, p)) :
    planReqRefusal r = some (PlannerRefusal.ciDisagrees i w p) := by
  unfold planReqRefusal; rw [hev, h]; rfl

/-- **And a request paying both is refused by neither** (AGENTS §5.8: the checks do not bite a request that
agrees). -/
theorem planReqRefusal_of_a_request_paying_both (r : Planner.PlanReq) (hev : r.eveningInsideTheCalendar = true)
    (hci : r.ciDisagreement = none) : planReqRefusal r = none := by
  unfold planReqRefusal; rw [hev, hci]; rfl

/-- **And no refusal is a request paying both** — the converse, which the decoder's law below reads. -/
theorem planReqRefusal_eq_none_pays_both (r : Planner.PlanReq) (h : planReqRefusal r = none) :
    r.eveningInsideTheCalendar = true ∧ r.ciDisagreement = none := by
  unfold planReqRefusal at h
  cases hev : r.eveningInsideTheCalendar
  · rw [hev] at h; exact absurd h (by simp)
  · rw [hev] at h
    cases hci : r.ciDisagreement with
    | some x => rw [hci] at h; exact absurd h (by simp)
    | none =>
      -- every other branch names a refusal; this one is the request paying both clauses,
      -- which is the statement
      exact ⟨rfl, rfl⟩

/-- **Every request the decoder hands the planner pays D80's two clauses** — the hypothesis
`plan_places_no_demanding_block_after_wind_down` is discharged over (`PlannerWit`'s W-41 block): the assembler's every
successful path passes `planReqRefusal` answering `none`, asked but for the routines (`planReqRefusal_ignores_the_routines`). -/
theorem planReqOf_pays_the_evening_and_the_ci (parts : CapParts) (bm : Nat) (q : PlannerIn) (r : Planner.PlanReq)
    (h : planReqOf parts bm q = .ok r) : r.eveningInsideTheCalendar = true ∧ r.ciDisagreement = none := by
  unfold planReqOf at h
  split at h; · cases h
  cases hc : parts.cands <;> simp only [hc] at h <;> (split at h; · cases h) <;> (split at h; · cases h) <;>
    (split at h; · cases h) <;> (rename_i hnone; split at h; · cases h) <;>
    (cases h; have hpay := planReqRefusal_eq_none_pays_both _ hnone; exact hpay)

/-- **The two refusals spell themselves** — the texts a host reads (`tm_core::planwire::planner_refusal`). -/
theorem the_d80_refusals_spell_themselves :
    PlannerRefusal.eveningPastTheCalendar.text = "eveningPastTheCalendar" ∧
    (PlannerRefusal.ciDisagrees "m2".toList 0 (some 5)).text = "ciDisagrees m2 wire 0 plan 5" ∧
    (PlannerRefusal.ciDisagrees "x9".toList 3 none).text = "ciDisagrees x9 wire 3 plan none" := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-- **The optional reader hands the interruption on, decided** (check 9's second pass, W-41): a reader that answered a
constant would be refused by `decide` here, where `readState_accepts_a_running_day`'s `rfl` alone could not say so —
and the interruption's start after `now` (1,001 against `readState`'s 1,000) is read since D78. -/
theorem readOptInterrupt_reads_the_interruption :
    (match readOptInterrupt (.obj [("interrupt".toList, .obj [("started".toList, .num 1001),
        ("id".toList, .str "m1".toList)])]) with
      | .ok (some x) => decide (x = ⟨some ⟨1001, 0⟩, some "m1".toList⟩) | _ => false) = true := by decide

/-! ## Three refusals no request reaches (README gap 4751; stage 6 W-46 track H)

R3 swaps the shipped planner for `Planner.dayPlan`, and this section can REFUSE a request where fork 4748911's
planner was total.  Gap 4751 asked, for every refusal, why the binary's request never meets it on a tree the fork
planned.  Three of them are answered here for EVERY request, not only the binary's: `planReqOf` checks a run, the
candidate cap and the walls' agreement, and each is already settled by the sections `EmitWire.runRowsP` reads first
— the capacity section refuses `day0WithoutLog` without a replay (D24) and a `log` answer carries its run exactly
when it carries its facts; `CapWire.readCands` refuses `tooManyCandidates` past `CapWire.maxCandidates`, which is
`Planner.maxCands` (`the_two_candidate_caps_are_one_number`); and an answered capacity section holds the walls of
the plan it was read against, indexed in its own zone at its own blocks.  The rest of the class is classified, with
its evidence, by `tm/tests/kernel_planner_refusals.rs`. -/

/-- A `mapM` in `Except` that answers keeps the list's length. -/
theorem except_mapM_length {ε α β : Type} (f : α → Except ε β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → ys.length = xs.length
  | [], ys, h => by
    simp only [List.mapM_nil] at h
    cases h; rfl
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok y =>
      rw [hx] at h
      cases hxs : xs.mapM f with
      | error e => simp [hxs] at h; cases h
      | ok zs =>
        simp only [hxs] at h
        cases h
        simp [except_mapM_length f xs zs hxs]

/-- **A candidate list the capacity section accepts holds at most `CapWire.maxCandidates` records.** -/
theorem readCands_within_the_cap {cap : JVal} {c : CapWire.CandReq}
    (h : CapWire.readCands cap = .ok (some c)) : c.items.length ≤ CapWire.maxCandidates := by
  unfold CapWire.readCands at h
  split at h
  · cases h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i xs _
        split at h
        · cases h
        · rename_i hle
          cases hl : CapWire.readCandList xs with
          | error e => rw [hl] at h; cases h
          | ok cs =>
            rw [hl] at h
            simp only [Except.map, Except.ok.injEq, Option.some.injEq] at h
            subst h
            have := except_mapM_length _ _ _ hl
            simp only [List.length_zipIdx] at this
            simp only [this]
            omega

/-- **What a capacity request kept, read back** (`runCapZP`'s `CapParts`). -/
theorem runCapZP_parts {j cap : JVal} {zo : Option Cal.Tz} {v : JVal} {p : CapParts}
    (h : runCapZP j cap zo = .ok (v, p)) :
    logSectionWith j zo = .ok p.lg ∧
      CapWire.readCapacityZ p.plan.val p.clock zo (p.lg.bind LogAnswer.facts) p.sec = .ok p.cap ∧
      CapWire.readCands p.sec = .ok p.cands := by
  unfold runCapZP at h
  cases hlg : logSectionWith j zo with
  | error e => rw [hlg] at h; cases h
  | ok lg =>
    rw [hlg] at h
    cases hl : runLoad j with
    | error e => rw [hl] at h; cases h
    | ok t =>
      obtain ⟨plan, cmds, clock⟩ := t
      rw [hl] at h
      simp only at h
      cases hc : CapWire.readCapacityZ plan.val clock zo (lg.bind LogAnswer.facts) cap with
      | error r => rw [hc] at h; cases h
      | ok c =>
        rw [hc] at h
        simp only at h
        cases hq : CapWire.readCands cap with
        | error r => rw [hq] at h; cases h
        | ok q =>
          rw [hq] at h
          simp only at h
          cases cmds with
          | cons _ _ => cases h
          | nil =>
            simp only at h
            cases hr : runPlan plan [] with
            | error e => rw [hr] at h; cases h
            | ok r =>
              rw [hr] at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact ⟨rfl, hc, hq⟩

/-- **The parts the rows hand the planner are a capacity request's.** -/
theorem runRowsP_parts {j r : JVal} {p : CapParts} (h : EmitWire.runRowsP j = .ok (r, some p)) :
    ∃ cap zo v, runCapZP j cap zo = .ok (v, p) := by
  have hcap : ∀ v, runCapP j = .ok (v, some p) → ∃ cap zo v, runCapZP j cap zo = .ok (v, p) := by
    intro v hv
    unfold runCapP at hv
    cases hc : jget j "capacity" with
    | error e => rw [hc] at hv; cases hv
    | ok o =>
      rw [hc] at hv
      cases o with
      | none =>
        simp only at hv
        cases hw : runWithEmit j with
        | error e => rw [hw] at hv; cases hv
        | ok w => rw [hw] at hv; cases hv
      | some cap =>
        simp only at hv
        cases hz : zoneOf j with
        | error e => rw [hz] at hv; cases hv
        | ok zo =>
          rw [hz] at hv
          simp only at hv
          cases hp : runCapZP j cap zo with
          | error e => rw [hp] at hv; cases hv
          | ok vp =>
            obtain ⟨v', p'⟩ := vp
            rw [hp] at hv
            simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hv
            obtain ⟨-, rfl⟩ := hv
            exact ⟨cap, zo, v', hp⟩
  unfold EmitWire.runRowsP at h
  cases hplan : jget j "plan" with
  | error e => rw [hplan] at h; cases h
  | ok o =>
    rw [hplan] at h
    cases o with
    | none => exact hcap r h
    | some sec =>
      simp only at h
      cases hc : runCapP j with
      | error e => rw [hc] at h; cases h
      | ok vp =>
        obtain ⟨v, parts⟩ := vp
        rw [hc] at h
        simp only at h
        cases hz : zoneOf j with
        | error e => rw [hz] at h; cases h
        | ok zo =>
          rw [hz] at h
          cases zo with
          | none => cases h
          | some z =>
            simp only at h
            cases hl : runLoad j with
            | error e => rw [hl] at h; cases h
            | ok t =>
              obtain ⟨pl, cmds, clock⟩ := t
              rw [hl] at h
              simp only at h
              cases cmds with
              | cons _ _ => cases h
              | nil =>
                simp only at h
                cases hb : clock.blockMin with
                | none => rw [hb] at h; cases h
                | some bm =>
                  rw [hb] at h
                  simp only at h
                  cases hs : EmitWire.readRowSection sec with
                  | error x => rw [hs] at h; cases h
                  | ok q =>
                    rw [hs] at h
                    simp only [Except.ok.injEq, Prod.mk.injEq] at h
                    obtain ⟨-, rfl⟩ := h
                    exact hcap v hc

/-- `Look.mkInput?` hands its input's zone, day and walls through unchanged. -/
theorem mkInput?_keeps_the_zone_the_day_and_the_walls {x : Look.InputIn} {I : Look.Input}
    (h : Look.mkInput? x = .ok I) : I.walls = x.walls ∧ I.tz = x.tz ∧ I.day = x.day := by
  unfold Look.mkInput? at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h; exact ⟨rfl, rfl, rfl⟩

/-- **A capacity section that answers holds the walls of the plan it was read against**, indexed in
its own zone at its own blocks — the condition `planReqOf` checks before it assembles a request. -/
theorem readCapacityZ_walls {plan : PlanCore} {clock : ReqClock} {zo : Option Cal.Tz}
    {rep : Option Seal.Answer} {cap : JVal} {c : CapWire.CapReq}
    (h : CapWire.readCapacityZ plan clock zo rep cap = .ok c) :
    c.look.walls = Look.wallIndex c.look.tz c.look.day.cut.blockMin plan := by
  unfold CapWire.readCapacityZ at h
  obtain ⟨today, -, h⟩ := capBind_ok_elim h
  obtain ⟨bm, -, h⟩ := capBind_ok_elim h
  obtain ⟨z, -, h⟩ := capBind_ok_elim h
  obtain ⟨s, hs, h⟩ := capBind_ok_elim h
  obtain ⟨w, -, h⟩ := capBind_ok_elim h
  obtain ⟨T, -, h⟩ := capBind_ok_elim h
  obtain ⟨I, hI, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  cases h
  obtain ⟨hw, ht, hd⟩ := mkInput?_keeps_the_zone_the_day_and_the_walls (CapWire.mapError_ok hI)
  obtain ⟨-, -, -, hdb, -⟩ := CapWire.readSection_ok hs
  show I.walls = Look.wallIndex I.tz I.day.cut.blockMin plan
  rw [hw, ht, hd]
  simp only [CapWire.Section.input, hdb]

/-- **Without a replay a capacity section never answers**: day 0 is the replay's (D24), and a
section handed none is refused before it is built. -/
theorem readCapacityZ_needs_a_replay {plan : PlanCore} {clock : ReqClock} {zo : Option Cal.Tz}
    {cap : JVal} {c : CapWire.CapReq} :
    CapWire.readCapacityZ plan clock zo none cap ≠ .ok c := by
  intro h
  unfold CapWire.readCapacityZ at h
  obtain ⟨today, -, h⟩ := capBind_ok_elim h
  obtain ⟨bm, -, h⟩ := capBind_ok_elim h
  obtain ⟨z, -, h⟩ := capBind_ok_elim h
  obtain ⟨s, -, h⟩ := capBind_ok_elim h
  obtain ⟨w, -, h⟩ := capBind_ok_elim h
  obtain ⟨T, hT, -⟩ := capBind_ok_elim h
  simp [CapWire.Section.today0] at hT

/-- Law 13's check passes the seam's two values through untouched. -/
theorem within53A_ok {f : Option Seal.Answer} {rn : Option Seal.Run} {v : JVal} {a : LogAnswer}
    (h : within53A f rn v = .ok a) : a.facts = f ∧ a.run = rn := by
  unfold within53A at h
  cases hw : within53 v with
  | error e => rw [hw] at h; cases h
  | ok w => rw [hw] at h; cases h; exact ⟨rfl, rfl⟩

/-- **A `log` op that answers carries its run exactly when it carries its facts.** -/
theorem logOpZ_run_iff_facts {r : VLogReq} {a : LogAnswer} (h : logOpZ r = .ok a) :
    a.run.isSome = a.facts.isSome := by
  unfold logOpZ at h
  dsimp only at h
  split at h
  · obtain ⟨hf, hr⟩ := within53A_ok h
    rw [hf, hr]; rfl
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i run _
          split at h
          · cases h
          · obtain ⟨hf, hr⟩ := within53A_ok h
            rw [hf, hr]
            exact (the_seam_carries_its_run_exactly_when_it_carries_its_facts r.val run).symm

/-- **A `log` section that answers carries its run exactly when it carries its facts.** -/
theorem logSectionWith_run_iff_facts {j : JVal} {zo : Option Cal.Tz} {a : LogAnswer}
    (h : logSectionWith j zo = .ok (some a)) : a.run.isSome = a.facts.isSome := by
  unfold logSectionWith at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain ⟨r, -, hop, -⟩ := logAnswerOf_carries_the_op _ _ _ a h
      exact logOpZ_run_iff_facts hop
  · cases h

/-- **D80's two refusals are the only ones the finished request can carry** (`planReqRefusal`). -/
theorem planReqRefusal_names {r : Planner.PlanReq} {y : PlannerRefusal} (h : planReqRefusal r = some y) :
    y = .eveningPastTheCalendar ∨ ∃ i w p, y = .ciDisagrees i w p := by
  unfold planReqRefusal at h
  split at h
  · simp only [Option.some.injEq] at h; exact .inl h.symm
  · cases hd : r.ciDisagreement with
    | none => rw [hd] at h; cases h
    | some d =>
      rw [hd] at h
      simp only [Option.map, Option.some.injEq] at h
      exact .inr ⟨d.1, d.2.1, d.2.2, h.symm⟩

/-- **Once the run is there, the candidates are within the cap and the walls agree, `planReqOf` refuses only by D80's
two or by a routine's refusal** — in that order since W-46 (README gap 4795): `planReqRefusal` is asked of the
request before `Planner.mkRoutines?` reads the routines. -/
theorem planReqOf_refuses_only_by_d80_or_a_routine {parts : CapParts} {bm : Nat} {q : PlannerIn} {run : Seal.Run}
    (hrun : parts.lg.bind LogAnswer.run = some run)
    (hcap : (match parts.cands with | none => [] | some c => c.items).length ≤ Planner.maxCands)
    (hw : parts.cap.look.walls =
      Look.wallIndex parts.cap.look.tz parts.cap.look.day.cut.blockMin parts.plan.val)
    {x : PlannerRefusal} (hx : planReqOf parts bm q = .error x) :
    (x = .eveningPastTheCalendar ∨ ∃ i w p, x = .ciDisagrees i w p) ∨ ∃ e, x = .routineRefused e := by
  unfold planReqOf at hx
  rw [hrun] at hx
  simp only at hx
  rw [show Capped.ofList? (match parts.cands with | none => [] | some c => c.items)
      = some ⟨_, hcap⟩ from dif_pos hcap] at hx
  simp only at hx
  rw [if_neg (fun hne => hne hw)] at hx
  split at hx
  · rename_i y hy
    cases hx
    exact .inl (planReqRefusal_names hy)
  · split at hx
    · cases hx
      exact .inr ⟨_, rfl⟩
    · cases hx

/-- **Three of the planner section's refusals name a state no request reaches** (README gap 4751, stage 6 W-46
track H).  Whenever the rows and the capacity section have answered (`EmitWire.runRowsP` hands the parts over),
the assembler is never the one to refuse: the replay is there (`runAbsent` — the capacity section refuses
`day0WithoutLog` before it answers without one, and a `log` answer carries its run exactly when it carries its
facts), the candidates are within the cap (`candsPastCap` — `CapWire.readCands` refuses `tooManyCandidates` past
the same number, `the_two_candidate_caps_are_one_number`), and the capacity section's walls are the loaded plan's
in its own zone at its own blocks (`wallsDisagree`).  So for EVERY request, and not only the binary's, these three
come from nothing — a stronger statement than the encoder's bound, and the one gap 4751 asked a proof for. -/
theorem planReqOf_never_refuses_what_the_capacity_section_excludes {j r : JVal} {parts : CapParts}
    (hr : EmitWire.runRowsP j = .ok (r, some parts)) (bm : Nat) (q : PlannerIn) :
    planReqOf parts bm q ≠ .error .runAbsent ∧ planReqOf parts bm q ≠ .error .candsPastCap ∧
      planReqOf parts bm q ≠ .error .wallsDisagree := by
  obtain ⟨cap, zo, v, hz⟩ := runRowsP_parts hr
  obtain ⟨hlg, hcz, hcands⟩ := runCapZP_parts hz
  obtain ⟨run, hrun⟩ : ∃ run, parts.lg.bind LogAnswer.run = some run := by
    cases hl : parts.lg with
    | none => rw [hl] at hcz; exact absurd hcz readCapacityZ_needs_a_replay
    | some a =>
      cases hf : a.facts with
      | none =>
        rw [hl] at hcz
        simp only [Option.bind, hf] at hcz
        exact absurd hcz readCapacityZ_needs_a_replay
      | some _ =>
        have hi := logSectionWith_run_iff_facts (hl ▸ hlg)
        rw [hf] at hi
        cases hra : a.run with
        | none => rw [hra] at hi; cases hi
        | some rn => exact ⟨rn, by simp [Option.bind, hra]⟩
  have hw := readCapacityZ_walls hcz
  have hcap : (match parts.cands with | none => [] | some c => c.items).length ≤ Planner.maxCands := by
    cases hc : parts.cands with
    | none => simp [Planner.maxCands]
    | some c =>
      rw [hc] at hcands
      rw [← the_two_candidate_caps_are_one_number]
      exact readCands_within_the_cap hcands
  have hall : ∀ x, planReqOf parts bm q = .error x →
      x ≠ .runAbsent ∧ x ≠ .candsPastCap ∧ x ≠ .wallsDisagree := by
    intro x hx
    rcases planReqOf_refuses_only_by_d80_or_a_routine hrun hcap hw hx with (h | ⟨i, w, p, h⟩) | ⟨e, h⟩ <;>
      subst h <;> exact ⟨by simp, by simp, by simp⟩
  refine ⟨fun h => (hall _ h).1 rfl, fun h => (hall _ h).2.1 rfl, fun h => (hall _ h).2.2 rfl⟩

/-! ### Two refusals of a routine no section the reader accepts, or no request the host's encoder builds, reaches
(README gaps 4793 and 4795; stage 6 W-46 track H)

`Planner.mkRoutine?` refuses an instance by five names.  Two of them are now shadowed for good: `pastTheHorizon` by the
section's own reader, which bounds every `winHi` by the very bound `mkRoutine?` refuses past; and `unknownItem` by D80's
`ci` clause, asked first since W-46, on every request whose routines each name a candidate it carries — which the host's
encoder pays by construction, reading every instance off a candidate it sends. -/

/-- **D80's two clauses read no routine** (README gap 4795): the evening reads the lookahead input, the day and the run,
and the `ci` clause the candidates and the plan, so a request and the same request with other routines are refused alike
— which is what lets `planReqOf` ask D80 before it reads the routines. -/
theorem planReqRefusal_ignores_the_routines (r : Planner.PlanReq) (rs : Capped RoutineIn) :
    planReqRefusal { r with routines := rs } = planReqRefusal r := rfl

/-- An answer of a `mapM` in `Except` is the image of members of the list. -/
theorem except_mapM_mem {ε α β : Type} (f : α → Except ε β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h, y, hy => by
    simp only [List.mapM_nil] at h
    cases h; cases hy
  | x :: xs, ys, h, y, hy => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok b =>
      rw [hx] at h
      cases hxs : xs.mapM f with
      | error e => simp [hxs] at h; cases h
      | ok zs =>
        simp only [hxs] at h
        cases h
        rcases List.mem_cons.1 hy with rfl | hz
        · exact ⟨x, List.mem_cons.2 (.inl rfl), hx⟩
        · obtain ⟨w, hw, hfw⟩ := except_mapM_mem f xs zs hxs y hz
          exact ⟨w, List.mem_cons.2 (.inr hw), hfw⟩

/-- A refusal of a `mapM` in `Except` is a member's refusal. -/
theorem except_mapM_error {ε α β : Type} (f : α → Except ε β) :
    ∀ (xs : List α) (e : ε), xs.mapM f = .error e → ∃ x ∈ xs, f x = .error e
  | [], e, h => by
    simp only [List.mapM_nil] at h
    cases h
  | x :: xs, e, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e' =>
      rw [hx] at h
      cases h
      exact ⟨x, List.mem_cons.2 (.inl rfl), hx⟩
    | ok b =>
      rw [hx] at h
      cases hxs : xs.mapM f with
      | error e' =>
        simp only [hxs] at h
        cases h
        obtain ⟨w, hw, hfw⟩ := except_mapM_error f xs _ hxs
        exact ⟨w, List.mem_cons.2 (.inr hw), hfw⟩
      | ok zs => simp [hxs] at h; cases h

/-- **A second `EmitWire.secWithin` accepts is the second it read, and inside the calendar.** -/
theorem secWithin_ok {ρ : Type} {r : ρ} {sec s : Nat} (h : EmitWire.secWithin r sec = .ok s) :
    s = sec ∧ sec < LogStamp.yearEnd := by
  unfold EmitWire.secWithin Cal.mkInstant? at h
  by_cases hw : Cal.Instant.wf ⟨sec, 0⟩ = true
  · rw [dif_pos hw] at h
    cases h
    refine ⟨rfl, ?_⟩
    have h2 : sec < 315537897600 := by
      simp [Cal.Instant.wf] at hw
      omega
    exact h2
  · rw [dif_neg hw] at h
    cases h

/-- **A routine the reader accepts closes inside the calendar** — its `winHi` is `EmitWire.secWithin`'s answer. -/
theorem readRoutine_closes_inside_the_calendar {i : Nat} {v : JVal} {x : RoutineIn} (h : readRoutine i v = .ok x) :
    x.winHi < LogStamp.yearEnd := by
  unfold readRoutine at h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  dsimp only at h
  split at h <;>
  · obtain ⟨_, -, h⟩ := capBind_ok_elim h
    obtain ⟨_, -, h⟩ := capBind_ok_elim h
    obtain ⟨_, -, h⟩ := capBind_ok_elim h
    obtain ⟨_, -, h⟩ := capBind_ok_elim h
    obtain ⟨_, hhi, h⟩ := capBind_ok_elim h
    obtain ⟨_, -, h⟩ := capBind_ok_elim h
    obtain ⟨_, -, h⟩ := capBind_ok_elim h
    obtain ⟨_, -, h⟩ := capBind_ok_elim h
    cases h
    obtain ⟨rfl, hlt⟩ := secWithin_ok hhi
    exact hlt

/-- **Every routine the section's reader accepts closes inside the calendar.** -/
theorem readPlannerSection_routines_close_inside_the_calendar {now : Cal.Instant} {sec : JVal} {q : PlannerIn}
    (h : readPlannerSection now sec = .ok q) : ∀ x ∈ q.routines, x.winHi < LogStamp.yearEnd := by
  unfold readPlannerSection at h
  obtain ⟨_, -, h⟩ := capBind_ok_elim h
  dsimp only at h
  split at h <;>
  · obtain ⟨_, -, h⟩ := capBind_ok_elim h
    obtain ⟨_, -, h⟩ := capBind_ok_elim h
    split at h
    · obtain ⟨rs, hrs, h⟩ := capBind_ok_elim h
      obtain ⟨_, -, h⟩ := capBind_ok_elim h
      cases h; cases hrs
      intro x hx; cases hx
    · obtain ⟨rs, hrs, h⟩ := capBind_ok_elim h
      obtain ⟨_, -, h⟩ := capBind_ok_elim h
      cases h
      intro x hx
      unfold readRoutines at hrs
      obtain ⟨p, -, hp⟩ := except_mapM_mem _ _ _ hrs x hx
      exact readRoutine_closes_inside_the_calendar hp
    · obtain ⟨rs, hrs, h⟩ := capBind_ok_elim h
      cases hrs

/-- **`Planner.mkRoutines?` answers `pastTheHorizon` only for an instance that closes outside the calendar.** -/
theorem mkRoutines?_past_the_horizon {p : PlanCore} {xs : List RoutineIn} {i : Id}
    (h : Planner.mkRoutines? p xs = .error (.pastTheHorizon i)) : ∃ x ∈ xs, LogStamp.yearEnd ≤ x.winHi := by
  unfold Planner.mkRoutines? at h
  split at h
  · cases h
  · split at h
    · rename_i e he
      cases h
      obtain ⟨x, hx, hxe⟩ := except_mapM_error _ _ _ he
      refine ⟨x, hx, ?_⟩
      unfold Planner.mkRoutine? at hxe
      split at hxe
      · cases hxe
      · split at hxe
        · cases hxe
        · split at hxe
          · cases hxe
          · split at hxe
            · assumption
            · split at hxe <;> cases hxe
    · split at h <;> cases h

/-- **And `unknownItem` only for an instance whose item its plan does not hold.** -/
theorem mkRoutines?_unknown_item {p : PlanCore} {xs : List RoutineIn} {i : Id}
    (h : Planner.mkRoutines? p xs = .error (.unknownItem i)) : ∃ x ∈ xs, p.store.get x.id = none := by
  unfold Planner.mkRoutines? at h
  split at h
  · cases h
  · split at h
    · rename_i e he
      cases h
      obtain ⟨x, hx, hxe⟩ := except_mapM_error _ _ _ he
      refine ⟨x, hx, ?_⟩
      unfold Planner.mkRoutine? at hxe
      split at hxe
      · rename_i hn
        exact Option.isNone_iff_eq_none.1 hn
      · split at hxe
        · cases hxe
        · split at hxe
          · cases hxe
          · split at hxe
            · cases hxe
            · split at hxe <;> cases hxe
    · split at h <;> cases h

/-- **`routineRefused pastTheHorizon` is answered to no section the reader accepts** (README gap 4793, narrowed): the
reader bounds every `winHi` by `EmitWire.secWithin` — `Cal.mkInstant?`'s bound, the very bound `Planner.mkRoutine?`
refuses past — so an instance closing outside the calendar is refused by the reader, `badRoutine <i> winHi`, before
the assembler sees it.  For EVERY request, not only the binary's. -/
theorem planReqOf_never_refuses_past_the_horizon {now : Cal.Instant} {sec : JVal} {q : PlannerIn}
    (hq : readPlannerSection now sec = .ok q) (parts : CapParts) (bm : Nat) (i : Id) :
    planReqOf parts bm q ≠ .error (.routineRefused (.pastTheHorizon i)) := by
  intro h
  have hwin := readPlannerSection_routines_close_inside_the_calendar hq
  unfold planReqOf at h
  split at h
  · cases h
  · cases hc : parts.cands <;> simp only [hc] at h <;>
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · rename_i y hy
            cases h
            rcases planReqRefusal_names hy with h1 | ⟨_, _, _, h1⟩ <;> cases h1
          · split at h
            · rename_i e he
              cases h
              obtain ⟨x, hx, hle⟩ := mkRoutines?_past_the_horizon he
              exact absurd (hwin x hx) (Nat.not_lt.2 hle)
            · cases h

/-- **`routineRefused unknownItem` is answered to no request whose every routine names a candidate it carries**
(README gap 4795): D80 is asked first (`planReqOf`), and a request that passes it holds every candidate's item —
`ciDisagreement` is none, and a candidate its plan does not hold disagrees, `plan none` — so a routine named by one
is held too.  The host's encoder reads every instance off a candidate it sends in the same request
(`tm_core::planwire::routine_instances` over the very list `planwire::capacity_json` sends), so on its requests the
routine's `unknownItem` is unreachable, and what such a request meets is P72's `ciDisagrees … plan none`. -/
theorem planReqOf_never_refuses_an_item_a_candidate_names (parts : CapParts) (bm : Nat) (q : PlannerIn)
    (hq : ∀ x ∈ q.routines, ∃ c, parts.cands = some c ∧ ∃ p ∈ c.items, p.1.id = x.id) (i : Id) :
    planReqOf parts bm q ≠ .error (.routineRefused (.unknownItem i)) := by
  intro h
  unfold planReqOf at h
  split at h
  · cases h
  · cases hc : parts.cands with
    | none =>
      simp only [hc] at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · rename_i y hy
            cases h
            rcases planReqRefusal_names hy with h1 | ⟨_, _, _, h1⟩ <;> cases h1
          · split at h
            · rename_i e he
              cases h
              obtain ⟨x, hx, -⟩ := mkRoutines?_unknown_item he
              obtain ⟨c, hc', -⟩ := hq x hx
              rw [hc] at hc'
              cases hc'
            · cases h
    | some c =>
      simp only [hc] at h
      split at h
      · cases h
      · rename_i cs hcs
        split at h
        · cases h
        · split at h
          · rename_i y hy
            cases h
            rcases planReqRefusal_names hy with h1 | ⟨_, _, _, h1⟩ <;> cases h1
          · rename_i hnone
            split at h
            · rename_i e he
              cases h
              obtain ⟨x, hx, hnx⟩ := mkRoutines?_unknown_item he
              obtain ⟨c', hc', p, hp, hpid⟩ := hq x hx
              rw [hc] at hc'
              cases hc'
              have hci := (planReqRefusal_eq_none_pays_both _ hnone).2
              have hmem : p ∈ cs.val := by
                unfold Capped.ofList? at hcs
                split at hcs
                · cases hcs; exact hp
                · cases hcs
              have hagree := (Planner.PlanReq.ciDisagreement_eq_none_iff _).1 hci p hmem
              unfold Planner.PlanReq.planCi at hagree
              rw [hpid] at hagree
              simp [hnx] at hagree
            · cases h

/-! ## D80 (a) before the section's refusals (README gap 4793; the W-46 repair)

On the calendar's last local day an evening routine's window runs past the calendar's last second, and the section's
reader refused it — `badRoutine <i> winLo` or `winHi` — before the assembler asked D80 (a), so a day P71's row names
`eveningPastTheCalendar` reached the host under another name (the W-46 switch's R3 BLOCKER).  `runPlanner` now hands a
section refusal to `eveningFirst` first.  The order's laws: `eveningFirst` names the evening and nothing else; a request
`planReqOf` builds passes it, so the order refuses no day the kernel plans; and over a section refusal it is P71's name
that reaches the host.  `runPlanner_refuses_a_section_the_decoder_refuses` gains the hypothesis that the evening is
inside the calendar: without it the statement is false on exactly that day (`kernel_planner_refusals.rs`' calendar
test is the witness, through the FFI), and `runPlanner_names_an_evening_past_the_calendar_over_a_section_refusal` is the
case it leaves out. -/

/-- **`eveningFirst` names the evening alone**: with no candidate, D80 (b) has nothing to disagree about. -/
theorem eveningFirst_names_only_the_evening (parts : CapParts) (x : PlannerRefusal)
    (h : eveningFirst parts = some x) : x = .eveningPastTheCalendar := by
  unfold eveningFirst at h
  cases hr : parts.lg.bind LogAnswer.run with
  | none => simp [hr] at h
  | some run =>
    simp only [hr, Option.bind_some] at h
    unfold planReqRefusal at h
    split at h
    · exact (Option.some.inj h).symm
    · nomatch h

/-- **The probe answers as the request whose evening it reads**, whatever the configuration it is handed. -/
theorem eveningFirst_probe_passes (r : Planner.PlanReq) (p : PrioCfg) (h : planReqRefusal r = none) :
    planReqRefusal ⟨r.plan, r.run, r.look, RuntimeIn.empty, Capped.nil, p, Capped.nil, none⟩ = none := by
  have he : Planner.PlanReq.eveningInsideTheCalendar
      ⟨r.plan, r.run, r.look, RuntimeIn.empty, Capped.nil, p, Capped.nil, none⟩ = r.eveningInsideTheCalendar := rfl
  unfold planReqRefusal
  rw [he, (planReqRefusal_eq_none_pays_both r h).1]
  rfl

/-- `eveningFirst_probe_passes` at the configuration `eveningFirst` builds, read off the request. -/
theorem eveningFirst_probe_of_a_request_passes (r : Planner.PlanReq) (h : planReqRefusal r = none) :
    planReqRefusal ⟨r.plan, r.run, r.look, RuntimeIn.empty, Capped.nil,
      ⟨r.prio.bins, r.prio.safety, r.prio.dflt, false, 0⟩, Capped.nil, none⟩ = none :=
  eveningFirst_probe_passes r _ h

/-- **A request `planReqOf` builds passes `eveningFirst`**: the assembler asked D80 (a) of the same evening, so the
order refuses no day the kernel plans. -/
theorem eveningFirst_passes_what_planReqOf_builds (parts : CapParts) (bm : Nat) (q : PlannerIn)
    (req : Planner.PlanReq) (h : planReqOf parts bm q = .ok req) : eveningFirst parts = none := by
  unfold planReqOf at h
  unfold eveningFirst
  split at h; · cases h
  rename_i run hrun
  simp only [hrun, Option.bind_some]
  cases hc : parts.cands <;> simp only [hc] at h <;> (split at h; · cases h) <;> (split at h; · cases h) <;>
    (split at h; · cases h) <;>
    (rename_i hnone; have hq := eveningFirst_probe_of_a_request_passes _ hnone; exact hq)

/-- **And a day `eveningFirst` refuses is never planned** — the assembler refuses it too. -/
theorem an_evening_eveningFirst_refuses_is_never_planned (parts : CapParts) (y : PlannerRefusal)
    (hg : eveningFirst parts = some y) (bm : Nat) (q : PlannerIn) (req : Planner.PlanReq) :
    planReqOf parts bm q ≠ .ok req := fun h => by
  rw [eveningFirst_passes_what_planReqOf_builds parts bm q req h] at hg
  cases hg

/-- **Over a section refusal, an evening past the calendar reaches the host by P71's name** — the case
`runPlanner_refuses_a_section_the_decoder_refuses` leaves out. -/
theorem runPlanner_names_an_evening_past_the_calendar_over_a_section_refusal (j sec r : JVal) (parts : CapParts)
    (x y : PlannerRefusal)
    (hp : jget j "planner" = .ok (some sec)) (hr : EmitWire.runRowsP j = .ok (r, some parts))
    (hs : readPlannerSection parts.cap.look.today0.now sec = .error x) (hg : eveningFirst parts = some y) :
    runPlanner j = .error (plannerRefusalJson PlannerRefusal.eveningPastTheCalendar) := by
  rw [eveningFirst_names_only_the_evening parts y hg] at hg
  simp only [runPlanner, hp, hr, hs, hg, Option.getD]

end PlanWire
end Tm
