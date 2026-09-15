import TmKernel.SealLaw
/-!
# SealResume — resuming a checkpoint over its tail (stage 5, D9, W2)

Design `kernel/design/stage5/stage5-D9-D10-design.md` §9.3 (the guards), §9.4 (the reseal) and §9.5 (the laws).
`resume z T K b term p` restores the state a checkpoint `K` holds (`restore`), masks the tail `b` with the settled undos
set aside (`unsettled`), refuses by G1 an undo whose target could be folded (`g1`), and steps the tail's survivors on
the stored wakes and the tail's (`tailIndex`, `tailSlept`), refusing by G2 a wake behind the cut or inside the fence,
and by G3 a reading of the index before the head second or a key below the horizons (`stepCheck`); every tail entry's
header is checked too (`headerCheck`).  The answer (`resumedAnswer`) is the resumed state grouped as `ckptOf` groups a
state, with the checkpoint's all-time aggregates below the horizons (`aggMerged`).

Nothing here is on the wire yet (W3 wires it).  D9-21: `restore` and the tail fold are `foldl`s; `unsettled` is
`filterTR`; `g1` reads `danglingOf` (a `foldl` whose steps scan the stack: quadratic on a hostile tail of undos, W5
measures it); `resumedAnswer` groups with `canon` (each insertion scans; W4's lever).
-/
namespace Tm
namespace Seal

open Replay (State Machine Effect HeaderRec EnergyObs Obs)
open Log (Entry)

/-! ## The guards' vocabulary -/

/-- **The fence** (G2): a surviving tail wake must be more than three days before every folded future instant, since
two instants on one local date are less than three days apart under any zone table (offsets are under a day). -/
def fenceSec : Nat := 259200

/-- The open block's running sub-segment start, if any. -/
def blockSince (m : Machine) : List Cal.Instant := ((m.block.bind (·.since)).map (·.1)).toList

/-- The open block's pause start, if any. -/
def blockPaused (m : Machine) : List Cal.Instant := ((m.block.bind (·.pausedAt)).map (·.1)).toList

/-- **Every instant a step reads the day index at**: the entry's own (`entryInstants`), and the open block's sub-segment
and pause starts when the step closes them (`closeSub`, `closePause`). -/
def stepQueries (m : Machine) (e : Entry) : List Cal.Instant :=
  entryInstants e ++
    match e.ev with
    | .start .. => blockSince m ++ blockPaused m
    | .pause id =>
      match m.block with
      | some b => if b.id = id ∧ b.paused = false then blockSince m else []
      | none => []
    | .unpause id =>
      match m.block with
      | some b => if b.id = id ∧ b.paused = true then blockPaused m else []
      | none => []
    | .interrupt _ => blockSince m ++ blockPaused m
    | .stop id _ =>
      match m.block with
      | some b => if b.id = id then blockSince m ++ blockPaused m else []
      | none => []
    | .done id .. =>
      match m.block with
      | some b => if b.id = id then blockSince m ++ blockPaused m else []
      | none => []
    | _ => []

/-- **The tail without its settled undos** (§7.4): a settled undo cancels nothing after the cut. -/
def unsettled (settled : List Nat) (bs : List Entry) : List Entry :=
  bs.filter (fun e => !(e.ev.isUndo && settled.contains e.line))

/-- G1 for one dangling tail undo: refused when a folded survivor may carry its tag. -/
def reachOf (K : Ckpt) (u : Entry) : Option Refusal :=
  match u.ev with
  | .undo of_ _ =>
    match K.tagLast.find? (fun p => p.1 == of_) with
    | some p => some (.undoReach u.line p.2)
    | none => if !Log.isKnownTag of_ && K.tagOverflow then some (.undoReach u.line 0) else none
  | _ => none

/-- **G1** (§7.4): the first undo of the unsettled tail that dangles there and whose tag a folded survivor may carry. -/
def g1 (K : Ckpt) (N : List Entry) : Option Refusal := ((Replay.danglingOf N).2.reverse).findSome? (reachOf K)

/-- **The tail's day index**: the stored wakes and the tail's surviving wakes. -/
def tailIndex (z : Cal.Tz) (K : Ckpt) (sv : List Entry) : List Cal.Instant :=
  Replay.keptWakes z (K.wakes ++ Replay.wakeInstants sv)

/-- **The tail's `slept_by_day`**: a day's first folded wake's, else its first tail wake's. -/
def tailSlept (z : Cal.Tz) (K : Ckpt) (kw : List Cal.Instant) (sv : List Entry) : Nat → Option Nat :=
  fun d => (Replay.KMap.get K.sleptByDay d).or (Replay.KMap.get (Replay.sleptByDay z kw sv) d)

/-- The refusal for a key below the horizons. -/
def keyRefusal (line : Nat) : Replay.Key → Refusal
  | .day d => .sealedDay line d
  | .itemDay _ d => .sealedWindow line d
  | .doneDate _ d => .sealedWindow line d
  | .instDate _ _ d => .sealedWindow line d
  | _ => .sealedDay line 0

/-- **One checked tail step**: its effects, and the first guard it fails (G3's head, G2, G3's keys). -/
def stepCheck (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (K : Ckpt) (st : State) (e : Entry) :
    List Effect × Option Refusal :=
  let fx := Replay.effectsWith z dy sl st e
  (fx, (((stepQueries st.machine e).find? (fun q => decide (q.sec < headSec K.ledgerDay))).map
          (fun _ => Refusal.sealedDay e.line (K.ledgerDay - 1)))
    <|> (if Replay.isWake e && !(K.maxT.all (· < e.t.val) && K.futureFloor.all (fun f => decide (e.t.val.sec + fenceSec < f.sec)))
         then some (.wakeBehindCut e.line e.t.val) else none)
    <|> ((fx.find? (fun x => !keyAtOrAbove K.ledgerDay (horizonOf K.ledgerDay) x.key)).map (fun x => keyRefusal e.line x.key)))

def tailFoldStep (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (K : Ckpt)
    (acc : State × Option Refusal) (e : Entry) : State × Option Refusal :=
  let r := stepCheck z dy sl K acc.1 e
  (Replay.applyEffects acc.1 r.1, acc.2 <|> r.2)

/-- **The tail's survivors stepped from a state**, with the first refusal. -/
def tailFold (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (K : Ckpt) (st : State) (sv : List Entry) :
    State × Option Refusal :=
  sv.foldl (tailFoldStep z dy sl K) (st, none)

/-- **Every tail entry's header** (G3, cancelled entries included): at or after the head second, on a day at or after
the ledger day. -/
def headerCheck (dy : Cal.Instant → Nat) (K : Ckpt) (bs : List Entry) : Option Refusal :=
  bs.findSome? (fun e => if e.t.val.sec < headSec K.ledgerDay then some (.sealedDay e.line (K.ledgerDay - 1))
    else if dy e.t.val < K.ledgerDay then some (.sealedDay e.line (dy e.t.val)) else none)

/-- **The tail's headers**: each entry's day on the tail's index and its mask bit (a settled undo is cancelled, as every
undo is; any other entry reads the unsettled tail's mask). -/
def tailHeaders (dy : Cal.Instant → Nat) (settled : List Nat) (bs : List Entry) : List (Nat × HeaderRec) :=
  let dead := Replay.maskFast (unsettled settled bs)
  (bs.foldl (fun (acc : List (Nat × HeaderRec) × Nat) e =>
    if e.ev.isUndo && settled.contains e.line then ((dy e.t.val, HeaderRec.of e true) :: acc.1, acc.2)
    else ((dy e.t.val, HeaderRec.of e (Replay.deadAt dead acc.2)) :: acc.1, acc.2 + 1)) ([], 0)).1.reverse

/-- The stored headers of a checkpoint's open days. -/
def storedHeaders (K : Ckpt) : List (Nat × HeaderRec) := K.openDays.flatMap (fun o => o.headers.map (fun h => (o.day, h)))

/-! ## The restored state -/

/-- Write every pair's value at its key, in order. -/
def writeAll {κ β : Type} [DecidableEq κ] [Replay.KeyHash κ] (l : List (κ × β)) (m : Replay.HMap κ β) : Replay.HMap κ β :=
  l.foldl (fun m p => m.alter p.1 (fun _ => some p.2)) m

/-- A checkpoint's window item minutes, as pairs. -/
def windowItemPairs (K : Ckpt) : List ((Nat × Log.Id) × Nat) :=
  K.window.flatMap (fun w => w.itemMin.map (fun p => ((w.day, p.1), p.2)))

/-- A checkpoint's window done dates, as pairs. -/
def windowDonePairs (K : Ckpt) : List ((Nat × Log.Id) × Unit) :=
  K.window.flatMap (fun w => w.doneIds.map (fun i => ((w.day, i), ())))

/-- A checkpoint's instances, the date-keyed then the others. -/
def instPairs (K : Ckpt) : List ((List Char × List Char) × Replay.InstRec) := K.window.flatMap (·.inst) ++ K.instOther

/-- Write a value at a key when there is one. -/
def writeOpt {κ β : Type} [DecidableEq κ] [Replay.KeyHash κ] (m : Replay.HMap κ β) (k : κ) : Option β → Replay.HMap κ β
  | some x => m.alter k (fun _ => some x)
  | none => m


def restore (K : Ckpt) (n : Nat) : State :=
  ⟨K.openDays.foldl (fun m o => writeOpt m o.day o.acc) (Replay.HMap.empty n),
   K.items.foldl (fun m a => writeOpt m a.id a.acc) (Replay.HMap.empty n),
   writeAll (windowItemPairs K) (Replay.HMap.empty n),
   K.openDays.flatMap (fun o => o.energy.reverse),
   K.openDays.flatMap (fun o => o.durations.reverse),
   K.openDays.flatMap (fun o => o.interrupts.reverse),
   [], K.machine, ⟨K.lastEff, 0⟩,
   K.items.foldl (fun m a => writeOpt m a.id a.lastDone) (Replay.HMap.empty n),
   writeAll (windowDonePairs K) (Replay.HMap.empty n),
   writeAll (instPairs K) (Replay.HMap.empty n),
   writeAll K.named (Replay.HMap.empty n),
   K.rwarns.reverse,
   K.openDays.flatMap (fun o => (o.demotions.map (fun r => (o.day, r))).reverse),
   K.openDays.flatMap (fun o => (o.closes.map (fun r => (o.day, r))).reverse),
   K.items.foldl (fun m a => if a.dropped then m.alter a.id (fun _ => some ()) else m) (Replay.HMap.empty n),
   K.longestLeak, K.unknown,
   K.openDays.foldl (fun m o => writeOpt m o.day o.seam) (Replay.HMap.empty n)⟩

/-- A non-start energy observation rebound to a `slept_by_day` (late binding, C5). -/
def rebindObs (g : Nat → Option Nat) (o : EnergyObs) : EnergyObs :=
  if o.fromStart then o else { o with sleptMin := g o.day }

/-- **A state's observations rebound** to a `slept_by_day`. -/
def rebindState (g : Nat → Option Nat) (st : State) : State := { st with energy := st.energy.map (rebindObs g) }

/-! ## The resumed answer -/

def minOpt : Option Nat → Option Nat → Option Nat
  | none, b => b
  | some a, none => some a
  | some a, some b => some (Nat.min a b)

def maxOpt : Option Nat → Option Nat → Option Nat
  | none, b => b
  | some a, none => some a
  | some a, some b => some (Nat.max a b)

/-- **One item's all-time facts after a resume**: the state's, with the first done date and the count of done dates
taking the checkpoint's dates below the horizon. -/
def aggMerged (K : Ckpt) (st : State) (i : Log.Id) : ItemAgg :=
  let old := findItem K.items i
  let ds := (st.doneDates.pairs.filter (fun p => decide (p.1.2 = i))).map (·.1.1)
  ⟨i, st.items.get i, st.lastDone.get i, (st.dropped.get i).isSome,
   minOpt (old.bind (·.doneFirst)) (Replay.minDay? ds),
   ((old.map (·.doneCount)).getD 0) - (K.window.filter (fun w => w.doneIds.contains i)).length + ds.length⟩

/-- **The answer of a resumed state** (§11.1's `Hot`): grouped as `ckptOf` groups a state, above the checkpoint's
horizons, with its aggregates below them. -/
def resumedAnswer (K : Ckpt) (st : State) (hs : List (Nat × HeaderRec)) (entries : Nat) (ws : List (Nat × Log.LWarn)) :
    Seal.Answer :=
  ⟨K.ledgerDay, horizonOf K.ledgerDay,
   (canon idLt (K.items.map (·.id) ++ itemIds st)).map (fun i => (aggMerged K st i).finish),
   windowsFrom st (horizonOf K.ledgerDay), instOtherOf st, namedOf st,
   (daysFrom st hs K.ledgerDay).map (OpenDay.finish st.machine),
   st.machine.block.map (fun b => ⟨b.id, b.started, b.workedMin, b.since, b.paused⟩),
   st.machine.interrupt.map (fun i => ⟨0, some i.1, none, i.2.1, i.2.2, 0, []⟩),
   maxOpt K.lastDay (Replay.maxDay? (st.days.pairs.map Prod.fst)),
   st.global.lastEffective, K.entryCount + entries, st.unknown, st.longestLeak, st.rwarns.reverse,
   (K.warnings ++ ws).take maxWarnings, K.warnings.length + K.warnOverflow + ws.length - maxWarnings⟩

/-! ## Resume -/

/-- What a resume computed, for its answer and its reseal. -/
structure Run where
  entries : List Entry
  unsettledTail : List Entry
  survivors : List Entry
  index : List Cal.Instant
  slept : Nat → Option Nat
  state : State
  headers : List (Nat × HeaderRec)
  answer : Seal.Answer

/-- **Resume, the guards and the answer** (§9.3): G0 (the zone, the cut), G4 (`now` below the ledger day), G1, then the
tail's steps (G2, G3) and headers (G3). -/
def resumeRun (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) : Except Refusal Run :=
  if K.tzKey ≠ z.val.key then .error .zone
  else if !(b.head?.all (fun l => l.n == K.cut + 1)) then .error .cutMismatch
  else if T < K.ledgerDay then .error (.nowBelowLedger T K.ledgerDay)
  else
    let bs := Log.lineEntries b
    let N := unsettled K.settled bs
    match g1 K N with
    | some r => .error r
    | none =>
      let sv := Replay.survivors N
      let kw := tailIndex z K sv
      let dy := Replay.dayOf z kw
      let sl := tailSlept z K kw sv
      let r := tailFold z dy sl K (restore K (K.items.length + K.openDays.length + bs.length)) sv
      match r.2 <|> headerCheck dy K bs with
      | some x => .error x
      | none =>
        let hs := storedHeaders K ++ tailHeaders dy K.settled bs
        let st := rebindState sl r.1
        .ok ⟨bs, N, sv, kw, sl, st, hs, resumedAnswer K st hs bs.length (Log.lineWarnings b)⟩

/-- The reseal of a run (W2, part 3 builds it). -/
def resealOf (_z : Cal.Tz) (_T : Nat) (_K : Ckpt) (_b : List Log.Line) (_terminated : Bool) (_p : Policy) (_r : Run) :
    Option Resealed := none

/-- **Resume** (§9.4): the answer, and with a policy, the reseal. -/
def resume (z : Cal.Tz) (T : Nat) (k : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Option Policy) :
    Except Refusal (Seal.Answer × Option Resealed) :=
  match resumeRun z T k b with
  | .error e => .error e
  | .ok r => .ok (r.answer, p.bind (fun q => resealOf z T k b terminated q r))

end Seal
end Tm
